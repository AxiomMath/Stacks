module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackRelocalize
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRelocalizeModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionStagePresentation
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateSquarePasting
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateSquarePastingSupplement
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackIsoInvariance
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackGlueing
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackSizeBound
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackSquareZeroEffective

/-!
# `Coh_{X/Y}` over `W` is `Coh_{Λ_h X/Λ_h Y}` over `S`

Let `h : W ⟶ S` be a morphism of a big fppf site and `f : X ⟶ Y` a finitely presented morphism of
algebraic spaces over `W`. An object of `Coh_{X/Y}` gives an object of `Coh_{Λ_h X/Λ_h Y}`
(`AlgebraicGeometry.Space.CoherentSituation.relocalizeObject`). On morphisms, the inverse images
along the morphisms of base changes commute with the transport of modules
(`relocalizeModuleSquare`), compatibly with composites and identities, which gives a functor
`Coh_{X/Y} ⥤ Coh_{Λ_h X/Λ_h Y}` over `Over.map h`. It is fully faithful, and every object of the
target is vertically isomorphic to a transport (its test scheme over `Λ_h Y` comes from a test
scheme over `Y`), so `Coh_{X/Y}`, read over `S` by Construction A of Stacks 04WT, is equivalent
over the site of `S` to `Coh_{Λ_h X/Λ_h Y}`. By Stacks 04X5, algebraicity of the latter gives
algebraicity of `Coh_{X/Y}` over `W`. With `S` the final scheme `Spec ℤ` this is the change of base
scheme in the proof of Stacks 09DS.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.relocalizeModuleSquare`: the commutation of the
  transport of modules with inverse images.
* `AlgebraicGeometry.Space.CoherentSituation.relocalizeCoherentFunctor`: the functor
  `Coh_{X/Y} ⥤ Coh_{Λ_h X/Λ_h Y}`.
* `AlgebraicGeometry.Space.CoherentSituation.relocalizeEquivalenceOver`: the equivalence over the
  site of `S`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isAlgebraicStack_of_relocalize`: algebraicity over
  `S` of `Coh_{Λ_h X/Λ_h Y}` gives algebraicity over `W` of `Coh_{X/Y}`.
* `AlgebraicGeometry.Space.CoherentSituation.isAlgebraicStack_of_artinInputs_overIntegers`: Stacks
  09DS over an arbitrary base scheme from the inputs of Artin's criterion over `Spec ℤ`, the size
  condition [-1] being supplied.

## References

* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {W S : Scheme.{u}} {hW : B.Contains W} {hS : B.Contains S}
  (h : B.obj hW ⟶ B.obj hS)

/-- **The comparison of inverse images with relocalization, along a triangle.** The composition
law `AlgebraicGeometry.Space.relocalizeModulePullbackIso_comp`, read along a morphism `χ` equal to
the composite `φ ≫ ψ` and with the comparisons reversed. -/
theorem relocalizeModulePullbackIso_symm_triangle {X Y Z : AlgebraicSpaces B W hW}
    {φ : X ⟶ Y} {ψ : Y ⟶ Z} {χ : X ⟶ Z} (hk : φ ≫ ψ = χ)
    (hφ : yoneda.relativelyRepresentable φ.hom) (hψ : yoneda.relativelyRepresentable ψ.hom)
    (hχ : yoneda.relativelyRepresentable χ.hom)
    (hk' : relocalizeHomSE B W S hW hS h φ ≫ relocalizeHomSE B W S hW hS h ψ =
      relocalizeHomSE B W S hW hS h χ) :
    (relocalizeModulePullbackIsoSE B W S hW hS h χ hχ).symm ≪≫
        Functor.isoWhiskerRight (modulePullbackTriangle B W hW hk)
          (relocalizeModulesEquivalenceSE B W S hW hS h X.2
            (relocalizeSpaceSE B W S hW hS h X).2).functor =
      Functor.isoWhiskerLeft
          (relocalizeModulesEquivalenceSE B W S hW hS h Z.2
            (relocalizeSpaceSE B W S hW hS h Z).2).functor
          (modulePullbackTriangle B S hS hk') ≪≫
        Functor.isoWhiskerRight (relocalizeModulePullbackIsoSE B W S hW hS h ψ hψ).symm
          (modulePullback B S hS (relocalizeHomSE B W S hW hS h φ)) ≪≫
        Functor.isoWhiskerLeft (modulePullback B W hW ψ)
          (relocalizeModulePullbackIsoSE B W S hW hS h φ hφ).symm := by
  subst hk
  have e₁ : modulePullbackTriangle B W hW (rfl : φ ≫ ψ = φ ≫ ψ) =
      (modulePullbackCompIso B W hW φ ψ).symm :=
    modulePullbackTriangle_rfl φ ψ
  have e₂ : modulePullbackTriangle B S hS hk' =
      (modulePullbackCompIso B S hS (relocalizeHomSE B W S hW hS h φ)
        (relocalizeHomSE B W S hW hS h ψ)).symm :=
    modulePullbackTriangle_rfl _ _
  rw [e₁, e₂]
  have c := congrArg Iso.inv (relocalizeModulePullbackIso_comp B W S hW hS h φ ψ hφ hψ hχ)
  simp only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Category.assoc] at c
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom]
  exact c.symm

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.CoherentSituation

universe u

variable {B : BigFppfSite.{u}} {W S : Scheme.{u}} {hW : B.Contains W} {hS : B.Contains S}
  (h : B.obj hW ⟶ B.obj hS) (D : CoherentSituation B W hW)

/-! ### The squares of inverse images -/

/-- The inverse images along a morphism of base changes and along its extension commute with the
relocalization of modules. -/
abbrev relocalizeTopSquare {T T' : SchemesOver D.Y} (b : T ⟶ T') :
    (D.relocalizeModules h T').functor ⋙
        modulePullback B S hS (relocalizeHomSE B W S hW hS h (D.relativeMap b)) ≅
      modulePullback B W hW (D.relativeMap b) ⋙ (D.relocalizeModules h T).functor :=
  (relocalizeModulePullbackIsoSE B W S hW hS h (D.relativeMap b)
    (relativelyRepresentable_baseChangeMap B W hW D.f b)).symm

/-- The inverse images along the extension of a morphism of base changes and along the induced
morphism of base changes of the extension commute with the inverse images along the
comparisons `(Λ_h X)_T ≅ Λ_h (X_T)`. -/
abbrev relocalizeBottomSquare {T T' : SchemesOver D.Y} (b : T ⟶ T') :
    modulePullback B S hS (D.relocalizeSpaceIso h T').inv ⋙
        modulePullback B S hS ((D.relocalize h).relativeMap (D.relocalizeTestMap h b)) ≅
      modulePullback B S hS (relocalizeHomSE B W S hW hS h (D.relativeMap b)) ⋙
        modulePullback B S hS (D.relocalizeSpaceIso h T).inv :=
  modulePullbackSquare B S hS rfl (D.relocalizeSpaceIso_inv_naturality h b)

/-- **The transport of modules commutes with the inverse images along morphisms of base
changes.** -/
def relocalizeModuleSquare {T T' : SchemesOver D.Y} (b : T ⟶ T') :
    D.relocalizeModuleFunctor h T' ⋙
        modulePullback B S hS ((D.relocalize h).relativeMap (D.relocalizeTestMap h b)) ≅
      modulePullback B W hW (D.relativeMap b) ⋙ D.relocalizeModuleFunctor h T :=
  Functor.pasteSquare (D.relocalizeTopSquare h b) (D.relocalizeBottomSquare h b)

/-- The square at a composite is the pasting of the squares of the two factors. -/
theorem relocalizeModuleSquare_comp {T T' T'' : SchemesOver D.Y} (b : T ⟶ T')
    (b' : T' ⟶ T'') :
    D.relocalizeModuleSquare h (b ≫ b') ≪≫
        Functor.isoWhiskerRight (D.compComparison b b') (D.relocalizeModuleFunctor h T) =
      Functor.isoWhiskerLeft (D.relocalizeModuleFunctor h T'')
          ((D.relocalize h).compComparison (D.relocalizeTestMap h b)
            (D.relocalizeTestMap h b')) ≪≫
        Functor.isoWhiskerRight (D.relocalizeModuleSquare h b')
          (modulePullback B S hS ((D.relocalize h).relativeMap (D.relocalizeTestMap h b))) ≪≫
        Functor.isoWhiskerLeft (modulePullback B W hW (D.relativeMap b'))
          (D.relocalizeModuleSquare h b) := by
  have hk' : relocalizeHomSE B W S hW hS h (D.relativeMap b) ≫
      relocalizeHomSE B W S hW hS h (D.relativeMap b') =
        relocalizeHomSE B W S hW hS h (D.relativeMap (b ≫ b')) :=
    (relocalizeHom_comp h _ _).symm.trans
      (congrArg (relocalizeHomSE B W S hW hS h) (baseChangeMap_comp D.f b b').symm)
  exact Functor.pasteSquare_comp (D.compComparison b b') (modulePullbackTriangle B S hS hk')
    ((D.relocalize h).compComparison (D.relocalizeTestMap h b) (D.relocalizeTestMap h b'))
    (D.relocalizeTopSquare h b) (D.relocalizeTopSquare h b') (D.relocalizeTopSquare h (b ≫ b'))
    (D.relocalizeBottomSquare h b) (D.relocalizeBottomSquare h b')
    (D.relocalizeBottomSquare h (b ≫ b'))
    (relocalizeModulePullbackIso_symm_triangle h (baseChangeMap_comp D.f b b').symm _ _ _ hk')
    (modulePullbackSquare_comp (modulePushforwardCoherence B S hS)
      (baseChangeMap_comp (D.relocalize h).f (D.relocalizeTestMap h b)
        (D.relocalizeTestMap h b')).symm hk' rfl
      (D.relocalizeSpaceIso_inv_naturality h b) rfl
      (D.relocalizeSpaceIso_inv_naturality h b') rfl
      (D.relocalizeSpaceIso_inv_naturality h (b ≫ b')))

/-- The square depends on the morphism of test schemes only. -/
theorem relocalizeModuleSquare_congr {T T' : SchemesOver D.Y} {b b' : T ⟶ T'} (e : b = b') :
    D.relocalizeModuleSquare h b ≪≫
        Functor.isoWhiskerRight (D.relativeMapComparison e) (D.relocalizeModuleFunctor h T) =
      Functor.isoWhiskerLeft (D.relocalizeModuleFunctor h T')
          ((D.relocalize h).relativeMapComparison (congrArg (D.relocalizeTestMap h) e)) ≪≫
        D.relocalizeModuleSquare h b' := by
  subst e
  ext M
  simp [relativeMapComparison]

/-- **The square at an identity is the unit law.** -/
theorem relocalizeModuleSquare_id (T : SchemesOver D.Y) :
    D.relocalizeModuleSquare h (𝟙 T) ≪≫
        Functor.isoWhiskerRight (D.idComparison (modulePushforwardCoherence B W hW) T)
          (D.relocalizeModuleFunctor h T) ≪≫
        Functor.leftUnitor (D.relocalizeModuleFunctor h T) =
      Functor.isoWhiskerLeft (D.relocalizeModuleFunctor h T)
          ((D.relocalize h).idComparison (modulePushforwardCoherence B S hS)
            (D.relocalizeTest h T)) ≪≫
        Functor.rightUnitor (D.relocalizeModuleFunctor h T) :=
  Functor.unitLaw_of_compLaw (D.relocalizeModuleSquare h (𝟙 T))
    (D.relocalizeModuleSquare h (𝟙 T ≫ 𝟙 T)) (D.compComparison (𝟙 T) (𝟙 T))
    ((D.relocalize h).compComparison (D.relocalizeTestMap h (𝟙 T))
      (D.relocalizeTestMap h (𝟙 T)))
    (D.relativeMapComparison (Category.id_comp (𝟙 T)))
    ((D.relocalize h).relativeMapComparison
      (congrArg (D.relocalizeTestMap h) (Category.id_comp (𝟙 T))))
    (D.idComparison (modulePushforwardCoherence B W hW) T)
    ((D.relocalize h).idComparison (modulePushforwardCoherence B S hS) (D.relocalizeTest h T))
    (D.relocalizeModuleSquare_comp h (𝟙 T) (𝟙 T))
    (D.relocalizeModuleSquare_congr h (Category.id_comp (𝟙 T)))
    (idComparison_comp_fac (modulePushforwardCoherence B W hW) D (𝟙 T))
    (comp_idComparison_fac (modulePushforwardCoherence B S hS) (D.relocalize h)
      (𝟙 (D.relocalizeTest h T)))


/-! ### Transport of morphisms -/

/-- **The morphism of `Coh_{Λ_h X/Λ_h Y}` attached to a morphism of `Coh_{X/Y}`**: the extended
morphism of test schemes, with the comparison of modules conjugated by the square of
`AlgebraicGeometry.Space.CoherentSituation.relocalizeModuleSquare`. -/
def relocalizeCoherentHom {A A' : CoherentObject D} (m : CoherentHom A A') :
    CoherentHom (D.relocalizeObject h A) (D.relocalizeObject h A') where
  base := D.relocalizeTestMap h m.base
  fibre := Functor.conjFibre (D.relocalizeModuleSquare h m.base) m.fibre
  isIso_fibre := by
    have := m.isIso_fibre
    exact Functor.isIso_conjFibre (D.relocalizeModuleSquare h m.base) m.fibre

/-- The comparison of modules of the transported morphism is the comparison of `m` conjugated by
the square of `AlgebraicGeometry.Space.CoherentSituation.relocalizeModuleSquare`. -/
theorem relocalizeCoherentHom_fibre {A A' : CoherentObject D} (m : CoherentHom A A') :
    (D.relocalizeCoherentHom h m).fibre =
      Functor.conjFibre (D.relocalizeModuleSquare h m.base) m.fibre :=
  rfl

/-- The test scheme of the transport of `A` is the extension of the test scheme of `A`. -/
theorem relocalizeObject_T (A : CoherentObject D) :
    (D.relocalizeObject h A).T = D.relocalizeTest h A.T :=
  rfl

/-- The module of the transport of `A` is the transport of the module of `A`. -/
theorem relocalizeObject_F (A : CoherentObject D) :
    (D.relocalizeObject h A).F = (D.relocalizeModuleFunctor h A.T).obj A.F :=
  rfl

omit h D in
/-- The components of the unit law of Stacks 03LU at equal test schemes and equal modules. -/
theorem idComparison_app_heq {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {D' : CoherentSituation B S hS} (hc : ModulePushforwardCoherence B S hS)
    {T T' : SchemesOver D'.Y} (e : T = T')
    {M : Modules.{u, u} B S hS (D'.space T).1 (D'.space T).2}
    {M' : Modules.{u, u} B S hS (D'.space T').1 (D'.space T').2} (hM : HEq M M') :
    HEq ((D'.idComparison hc T).hom.app M) ((D'.idComparison hc T').hom.app M') := by
  subst e
  cases eq_of_heq hM
  rfl

/-- **Transport preserves identities.** -/
theorem relocalizeCoherentHom_id (A : CoherentObject D) :
    D.relocalizeCoherentHom h (CoherentHom.id (modulePushforwardCoherence B W hW) A) =
      CoherentHom.id (modulePushforwardCoherence B S hS) (D.relocalizeObject h A) := by
  have hcomp : HEq (((D.relocalize h).idComparison (modulePushforwardCoherence B S hS)
        (D.relocalizeTest h A.T)).hom.app ((D.relocalizeModuleFunctor h A.T).obj A.F))
      (((D.relocalize h).idComparison (modulePushforwardCoherence B S hS)
        (D.relocalizeObject h A).T).hom.app (D.relocalizeObject h A).F) :=
    idComparison_app_heq _ (D.relocalizeObject_T h A).symm
      (heq_of_eq (D.relocalizeObject_F h A).symm)
  refine coherentHom_eq_of_heq rfl ?_
  refine HEq.trans (heq_of_eq ((D.relocalizeCoherentHom_fibre h
      (CoherentHom.id (modulePushforwardCoherence B W hW) A)).trans
    ((congrArg (Functor.conjFibre (D.relocalizeModuleSquare h (𝟙 A.T)))
        (CoherentHom.id_fibre (modulePushforwardCoherence B W hW) A)).trans
      (Functor.conjFibre_id (D.relocalizeModuleSquare h (𝟙 A.T))
        (D.idComparison (modulePushforwardCoherence B W hW) A.T)
        ((D.relocalize h).idComparison (modulePushforwardCoherence B S hS)
          (D.relocalizeTest h A.T))
        (D.relocalizeModuleSquare_id h A.T) A.F)))) ?_
  exact HEq.trans hcomp (heq_of_eq (CoherentHom.id_fibre (modulePushforwardCoherence B S hS)
    (D.relocalizeObject h A)).symm)

/-- **Transport preserves composition.** -/
theorem relocalizeCoherentHom_comp {A A' A'' : CoherentObject D} (m : CoherentHom A A')
    (n : CoherentHom A' A'') :
    D.relocalizeCoherentHom h (m.comp n) =
      (D.relocalizeCoherentHom h m).comp (D.relocalizeCoherentHom h n) := by
  refine coherentHom_eq_of_heq rfl (heq_of_eq ?_)
  refine (D.relocalizeCoherentHom_fibre h (m.comp n)).trans ?_
  refine (congrArg (Functor.conjFibre (D.relocalizeModuleSquare h (m.base ≫ n.base)))
    (CoherentHom.comp_fibre m n)).trans ?_
  refine (Functor.conjFibre_fibreComp (D.compComparison m.base n.base)
    ((D.relocalize h).compComparison (D.relocalizeTestMap h m.base)
      (D.relocalizeTestMap h n.base))
    (D.relocalizeModuleSquare h m.base) (D.relocalizeModuleSquare h n.base) _
    (D.relocalizeModuleSquare_comp h m.base n.base) m.fibre n.fibre).trans ?_
  exact (CoherentHom.comp_fibre (D.relocalizeCoherentHom h m) (D.relocalizeCoherentHom h n)).symm

/-- The transport of modules along a test scheme is fully faithful. -/
def fullyFaithful_relocalizeModuleFunctor (T : SchemesOver D.Y) :
    (D.relocalizeModuleFunctor h T).FullyFaithful :=
  (D.relocalizeModules h T).fullyFaithfulFunctor.comp
    ((modulePushforwardCoherence B S hS).modulePullbackEquivalence
      (D.relocalizeSpaceIso h T).symm).fullyFaithfulFunctor

/-- Extending morphisms of test schemes is injective. -/
theorem relocalizeTestMap_injective {T T' : SchemesOver D.Y} {b b' : T ⟶ T'}
    (e : D.relocalizeTestMap h b = D.relocalizeTestMap h b') : b = b' :=
  CostructuredArrow.hom_ext _ _ (Over.OverMorphism.ext (congrArg (fun k => k.left.left) e))

/-- **Extending morphisms of test schemes is surjective.** A morphism of the extended test schemes
over `Λ_h Y` lies over `W`, because the structure morphisms to `W` are read off the morphisms to
`Λ_h Y`. -/
theorem exists_relocalizeTestMap_eq {T T' : SchemesOver D.Y}
    (g : D.relocalizeTest h T ⟶ D.relocalizeTest h T') :
    ∃ b : T ⟶ T', D.relocalizeTestMap h b = g := by
  let V : CostructuredArrow yoneda D.Y.1 := CostructuredArrow.mk (D.testChart T)
  let V' : CostructuredArrow yoneda D.Y.1 := CostructuredArrow.mk (D.testChart T')
  have hw : yoneda.map g.left ≫ relocalizeChart B W S hW hS h (D.testChart T') =
      relocalizeChart B W S hW hS h (D.testChart T) :=
    congrArg (fun k => k.hom) (CostructuredArrow.w g)
  let g' : (relocalizeChartsFunctor B W S hW hS h D.Y.1).obj V ⟶
      (relocalizeChartsFunctor B W S hW hS h D.Y.1).obj V' :=
    CostructuredArrow.homMk g.left hw
  obtain ⟨k, hk⟩ := (relocalizeChartsFunctor B W S hW hS h D.Y.1).map_surjective g'
  refine ⟨CostructuredArrow.homMk k.left (ObjectProperty.hom_ext _ (CostructuredArrow.w k)), ?_⟩
  have e := congrArg CommaMorphism.left hk
  exact CostructuredArrow.hom_ext _ _ e

/-- Transport of morphisms of `Coh_{X/Y}` is injective. -/
theorem relocalizeCoherentHom_injective {A A' : CoherentObject D} :
    Function.Injective (D.relocalizeCoherentHom h (A := A) (A' := A')) := by
  intro m n e
  have hb : m.base = n.base := D.relocalizeTestMap_injective h
    (congrArg (fun k : CoherentHom (D.relocalizeObject h A) (D.relocalizeObject h A') => k.base) e)
  obtain ⟨mb, mf, mi⟩ := m
  obtain ⟨nb, nf, ni⟩ := n
  change mb = nb at hb
  subst hb
  refine coherentHom_eq_of_heq rfl (heq_of_eq ?_)
  refine Functor.conjFibre_injective (D.relocalizeModuleSquare h mb)
    (D.fullyFaithful_relocalizeModuleFunctor h A.T) ?_
  have hmid : (D.relocalizeCoherentHom h (⟨mb, mf, mi⟩ : CoherentHom A A')).fibre =
      (D.relocalizeCoherentHom h (⟨mb, nf, ni⟩ : CoherentHom A A')).fibre :=
    eq_of_heq (heq_fibre_of_eq e)
  exact ((D.relocalizeCoherentHom_fibre h (⟨mb, mf, mi⟩ : CoherentHom A A')).symm.trans
    hmid).trans (D.relocalizeCoherentHom_fibre h (⟨mb, nf, ni⟩ : CoherentHom A A'))

/-- Every morphism between transports of objects of `Coh_{X/Y}` is the transport of a morphism. -/
theorem exists_relocalizeCoherentHom {A A' : CoherentObject D}
    (m : CoherentHom (D.relocalizeObject h A) (D.relocalizeObject h A')) :
    ∃ k : CoherentHom A A', D.relocalizeCoherentHom h k = m := by
  obtain ⟨mb, mf, mi⟩ := m
  obtain ⟨b, hb⟩ := D.exists_relocalizeTestMap_eq h mb
  subst hb
  have hE := D.fullyFaithful_relocalizeModuleFunctor h A.T
  let k : CoherentHom A A' := ⟨b, Functor.conjFibreInv (D.relocalizeModuleSquare h b) hE mf,
    Functor.isIso_conjFibreInv (D.relocalizeModuleSquare h b) hE mf mi⟩
  refine ⟨k, coherentHom_eq_of_heq rfl (heq_of_eq ?_)⟩
  exact (D.relocalizeCoherentHom_fibre h k).trans
    (Functor.conjFibre_conjFibreInv (D.relocalizeModuleSquare h b) hE mf)

/-! ### The functor -/

/-- **The functor `Coh_{X/Y} ⥤ Coh_{Λ_h X/Λ_h Y}`**, lying over `Over.map h`. -/
def relocalizeCoherentFunctor :
    @Functor (CoherentObject D) D.categoryData.category (CoherentObject (D.relocalize h))
      (D.relocalize h).categoryData.category :=
  letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  letI : Category.{u + 1} (CoherentObject (D.relocalize h)) :=
    (D.relocalize h).categoryData.category
  { obj := D.relocalizeObject h
    map := fun m => D.relocalizeCoherentHom h m
    map_id := fun A => D.relocalizeCoherentHom_id h A
    map_comp := fun m n => D.relocalizeCoherentHom_comp h m n }

/-- The transport functor lies over `Over.map h`. -/
theorem relocalizeCoherentFunctor_comp_projection :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    letI : Category.{u + 1} (CoherentObject (D.relocalize h)) :=
      (D.relocalize h).categoryData.category
    D.relocalizeCoherentFunctor h ⋙ coherentSiteProjection (D.relocalize h).categoryData =
      coherentSiteProjection D.categoryData ⋙ Over.map h := by
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  let : Category.{u + 1} (CoherentObject (D.relocalize h)) :=
    (D.relocalize h).categoryData.category
  exact CategoryTheory.Functor.hext (fun A => rfl) (fun A A' m => HEq.rfl)

/-- The transport functor `Coh_{X/Y} ⥤ Coh_{Λ_h X/Λ_h Y}` is faithful. -/
theorem relocalizeCoherentFunctor_faithful :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    letI : Category.{u + 1} (CoherentObject (D.relocalize h)) :=
      (D.relocalize h).categoryData.category
    (D.relocalizeCoherentFunctor h).Faithful :=
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  let : Category.{u + 1} (CoherentObject (D.relocalize h)) :=
    (D.relocalize h).categoryData.category
  ⟨fun e => D.relocalizeCoherentHom_injective h e⟩

/-- The transport functor `Coh_{X/Y} ⥤ Coh_{Λ_h X/Λ_h Y}` is full. -/
theorem relocalizeCoherentFunctor_full :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    letI : Category.{u + 1} (CoherentObject (D.relocalize h)) :=
      (D.relocalize h).categoryData.category
    (D.relocalizeCoherentFunctor h).Full :=
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  let : Category.{u + 1} (CoherentObject (D.relocalize h)) :=
    (D.relocalize h).categoryData.category
  ⟨fun m => D.exists_relocalizeCoherentHom h m⟩


/-! ### Objects of `Coh_{Λ_h X/Λ_h Y}` come from `Coh_{X/Y}` -/

omit h D in
/-- The isomorphism of base changes induced by an isomorphism of test schemes. -/
@[simps]
def relativeMapIso {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D' : CoherentSituation B S hS) {T T' : SchemesOver D'.Y} (e : T ≅ T') :
    D'.space T ≅ D'.space T' where
  hom := D'.relativeMap e.hom
  inv := D'.relativeMap e.inv
  hom_inv_id := by rw [← baseChangeMap_comp, e.hom_inv_id, baseChangeMap_id]
  inv_hom_id := by rw [← baseChangeMap_comp, e.inv_hom_id, baseChangeMap_id]

/-- The chart of `Λ_h Y` underlying a test scheme over `Λ_h Y`. -/
abbrev relocalizedChart (T' : SchemesOver (D.relocalize h).Y) :
    CostructuredArrow yoneda ((OverShriek.relocalizePresheafFunctor h).obj D.Y.1) :=
  CostructuredArrow.mk T'.hom.hom

/-- **The test scheme over `Y` whose extension is a given test scheme over `Λ_h Y`.** -/
def descendTest (T' : SchemesOver (D.relocalize h).Y) : SchemesOver D.Y :=
  CostructuredArrow.mk
    (Y := Over.mk (relocalizeChartBase B W S hW hS h (D.relocalizedChart h T')))
    (ObjectProperty.homMk (relocalizeChartDescent B W S hW hS h (D.relocalizedChart h T')) :
      (schemeSpaceFunctor B W hW).obj
        (Over.mk (relocalizeChartBase B W S hW hS h (D.relocalizedChart h T'))) ⟶ D.Y)

/-- The extension of the descended test scheme is the given one, up to an isomorphism which is
the identity on the underlying scheme. -/
def descendTestIso (T' : SchemesOver (D.relocalize h).Y) :
    D.relocalizeTest h (D.descendTest h T') ≅ T' :=
  CostructuredArrow.isoMk
    ((CostructuredArrow.proj _ _).mapIso
      (relocalizeChartsDescentIso B W S hW hS h (D.relocalizedChart h T')))
    (ObjectProperty.hom_ext _
      (CostructuredArrow.w
        (relocalizeChartsDescentIso B W S hW hS h (D.relocalizedChart h T')).hom))

/-- The inverse of `AlgebraicGeometry.Space.CoherentSituation.descendTestIso` is the identity on
the underlying scheme. -/
theorem descendTestIso_inv_left_left (T' : SchemesOver (D.relocalize h).Y) :
    (D.descendTestIso h T').inv.left.left = 𝟙 _ :=
  relocalizeChartsDescentIso_inv_left_left B W S hW hS h (D.relocalizedChart h T')

/-- The scheme of the site underlying the descended test scheme, read over `S`, is the given
one. -/
theorem relocalizeTest_descendTest_left (T' : SchemesOver (D.relocalize h).Y) :
    (Over.map h).obj (D.descendTest h T').left = T'.left :=
  congrArg Over.mk (relocalizeChartBase_comp B W S hW hS h (D.relocalizedChart h T'))

/-- The inverse of `AlgebraicGeometry.Space.CoherentSituation.descendTestIso`, as a morphism over
`S`, is the identification `T'.left = (Over.map h).obj (D.descendTest h T').left`. -/
theorem descendTestIso_inv_left (T' : SchemesOver (D.relocalize h).Y) :
    (D.descendTestIso h T').inv.left = eqToHom (D.relocalizeTest_descendTest_left h T').symm := by
  apply Over.OverMorphism.ext
  rw [D.descendTestIso_inv_left_left h T', Over.eqToHom_left]
  exact (eqToHom_refl _ _).symm

section Descend

variable (y : CoherentObject (D.relocalize h))

/-- The comparison `(Λ_h X)_{T'} ≅ (Λ_h X)_{Λ_h T}` of the base changes along a test scheme over
`Λ_h Y` and along the extension of its descent. -/
abbrev descendSpaceIso :
    (D.relocalize h).space y.T ≅
      (D.relocalize h).space (D.relocalizeTest h (D.descendTest h y.T)) :=
  (D.relocalize h).relativeMapIso (D.descendTestIso h y.T).symm

/-- The module of `y`, moved to `(Λ_h X)_{Λ_h T}`. -/
abbrev descendModule₁ :
    Modules.{u, u} B S hS ((D.relocalize h).space (D.relocalizeTest h (D.descendTest h y.T))).1
      ((D.relocalize h).space (D.relocalizeTest h (D.descendTest h y.T))).2 :=
  (modulePullback B S hS (D.descendSpaceIso h y).inv).obj y.F

/-- The module of `y`, moved to `Λ_h (X_T)`. -/
abbrev descendModule₂ :
    Modules.{u, u} B S hS (relocalizeSpaceSE B W S hW hS h (D.space (D.descendTest h y.T))).1
      (relocalizeSpaceSE B W S hW hS h (D.space (D.descendTest h y.T))).2 :=
  (modulePullback B S hS (D.relocalizeSpaceIso h (D.descendTest h y.T)).hom).obj
    (D.descendModule₁ h y)

/-- The inverse of `AlgebraicGeometry.Space.CoherentSituation.descendSpaceIso` and the projections
to the test schemes form a pullback square. -/
theorem isPullback_descendSpaceIso_inv :
    IsPullback (D.descendSpaceIso h y).inv
      ((D.relocalize h).projection (D.relocalizeTest h (D.descendTest h y.T)))
      ((D.relocalize h).projection y.T)
      ((schemeSpaceFunctor B S hS).map (D.descendTestIso h y.T).hom.left) :=
  isPullback_baseChangeMap (D.relocalize h).f (D.descendTestIso h y.T).hom

/-- The comparison `(Λ_h X)_{Λ_h T} ≅ Λ_h (X_T)` and the projections to the test schemes form a
pullback square. -/
theorem isPullback_relocalizeSpaceIso_hom (T : SchemesOver D.Y) :
    IsPullback (D.relocalizeSpaceIso h T).hom
      (relocalizeHomSE B W S hW hS h (D.projection T))
      ((D.relocalize h).projection (D.relocalizeTest h T))
      (relocalizeSchemeSpaceIso h T.left).hom :=
  IsPullback.of_horiz_isIso (CommSq.mk (D.relocalizeSpaceIso_hom_inclusion h T))

/-- The module `AlgebraicGeometry.Space.CoherentSituation.descendModule₁` is of finite
presentation. -/
theorem isFinitePresentationOnSite_descendModule₁ :
    (D.descendModule₁ h y).IsFinitePresentationOnSite :=
  (modulePullbackStabilityOfFinitePresentation B S hS).finitePresentation _ _ y.finitePresentation

/-- The module `AlgebraicGeometry.Space.CoherentSituation.descendModule₂` is of finite
presentation. -/
theorem isFinitePresentationOnSite_descendModule₂ :
    (D.descendModule₂ h y).IsFinitePresentationOnSite :=
  (modulePullbackStabilityOfFinitePresentation B S hS).finitePresentation _ _
    (D.isFinitePresentationOnSite_descendModule₁ h y)

/-- The module `AlgebraicGeometry.Space.CoherentSituation.descendModule₂` is flat over the
extension of the descended test scheme. -/
theorem isFlatOver_descendModule₂ :
    IsFlatOver B S hS (relocalizeSpaceSE B W S hW hS h (D.space (D.descendTest h y.T))).2
      (relocalizeHomSE B W S hW hS h (D.projection (D.descendTest h y.T))).hom
      (D.descendModule₂ h y) :=
  (modulePullbackStabilityOfFinitePresentation B S hS).flat
    (D.isPullback_relocalizeSpaceIso_hom h (D.descendTest h y.T)) _
    (D.isFinitePresentationOnSite_descendModule₁ h y)
    ((modulePullbackStabilityOfFinitePresentation B S hS).flat
      (D.isPullback_descendSpaceIso_inv h y) y.F y.finitePresentation y.flat)

/-- **The object of `Coh_{X/Y}` whose transport is a given object of `Coh_{Λ_h X/Λ_h Y}`.** -/
def descendObject : CoherentObject D where
  T := D.descendTest h y.T
  F := (D.relocalizeModules h (D.descendTest h y.T)).inverse.obj (D.descendModule₂ h y)
  finitePresentation := isFinitePresentationOnSite_relocalizeModulesEquivalence_inverse h _
    (D.isFinitePresentationOnSite_descendModule₂ h y)
  quasicoherent :=
    have := isFinitePresentationOnSite_relocalizeModulesEquivalence_inverse h _
      (D.isFinitePresentationOnSite_descendModule₂ h y)
    inferInstance
  flat := isFlatOver_relocalizeModulesEquivalence_inverseSE B W S hW hS h
    (D.projection (D.descendTest h y.T)).hom (D.space (D.descendTest h y.T)).2
    (relocalizeSpaceSE B W S hW hS h (D.space (D.descendTest h y.T))).2 _
    (D.isFlatOver_descendModule₂ h y)
  properSupport := by
    obtain ⟨hp, hU, hproper⟩ := y.properSupport
    have hfp := y.finitePresentation
    have hfp₁ := D.isFinitePresentationOnSite_descendModule₁ h y
    have sq₁ := D.isPullback_descendSpaceIso_inv h y
    have sq₂ := D.isPullback_relocalizeSpaceIso_hom h (D.descendTest h y.T)
    obtain ⟨hU₁, hproper₁⟩ := (modulePullbackStabilityOfFinitePresentation B S hS).properSupport
      sq₁ hp y.F y.quasicoherent inferInstance hU hproper
    have hp₁ := (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback sq₁ hp
    obtain ⟨hU₂, hproper₂⟩ := (modulePullbackStabilityOfFinitePresentation B S hS).properSupport
      sq₂ hp₁ _ inferInstance inferInstance hU₁ hproper₁
    have hp₂ := (isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback sq₂ hp₁
    have hp₀ : IsLocallyOfFiniteType B W hW (D.projection (D.descendTest h y.T)).hom :=
      (isLocallyOfFiniteType_relocalize_iff B W hW S hS h _).1 hp₂
    obtain ⟨hU₃, hproper₃⟩ := (hasProperSupport_relocalizeModulesEquivalence_inverse_iffSE B W S hW
      hS h (D.space (D.descendTest h y.T)).2
      ((schemeSpaceFunctor B W hW).obj (D.descendTest h y.T).left).2
      (D.projection (D.descendTest h y.T)).hom
      (relocalizeSpaceSE B W S hW hS h (D.space (D.descendTest h y.T))).2
      (relocalizeSpaceSE B W S hW hS h
        ((schemeSpaceFunctor B W hW).obj (D.descendTest h y.T).left)).2 hp₀
      (D.descendModule₂ h y)).2 ⟨hU₂, hproper₂⟩
    exact ⟨hp₀, hU₃, hproper₃⟩

/-- The test scheme of the descent of `y` is the descent of the test scheme of `y`. -/
theorem descendObject_T : (D.descendObject h y).T = D.descendTest h y.T :=
  rfl

/-- The comparison of modules of `AlgebraicGeometry.Space.CoherentSituation.descendHom`. -/
def descendFibreIso :
    (modulePullback B S hS (D.descendSpaceIso h y).hom).obj
        (D.relocalizeObject h (D.descendObject h y)).F ≅ y.F :=
  (modulePullback B S hS (D.descendSpaceIso h y).hom).mapIso
      (eqToIso (D.relocalizeObject_F h (D.descendObject h y)) ≪≫
        (modulePullback B S hS (D.relocalizeSpaceIso h (D.descendTest h y.T)).inv).mapIso
          ((D.relocalizeModules h (D.descendTest h y.T)).counitIso.app (D.descendModule₂ h y)) ≪≫
        (((modulePushforwardCoherence B S hS).modulePullbackEquivalence
          (D.relocalizeSpaceIso h (D.descendTest h y.T))).unitIso.app
            (D.descendModule₁ h y)).symm) ≪≫
    ((modulePushforwardCoherence B S hS).modulePullbackEquivalence
      (D.descendSpaceIso h y)).counitIso.app y.F

/-- **The comparison of an object of `Coh_{Λ_h X/Λ_h Y}` with the transport of its descent**,
over the identity of the underlying scheme. -/
def descendHom : CoherentHom y (D.relocalizeObject h (D.descendObject h y)) where
  base := (D.descendTestIso h y.T).inv
  fibre := (D.descendFibreIso h y).hom
  isIso_fibre := Iso.isIso_hom _

/-- The morphism of test schemes of `AlgebraicGeometry.Space.CoherentSituation.descendHom` is the
inverse of `AlgebraicGeometry.Space.CoherentSituation.descendTestIso`. -/
theorem descendHom_base : (D.descendHom h y).base = (D.descendTestIso h y.T).inv :=
  rfl

end Descend


/-! ### The equivalence over the site and the transfer of algebraicity -/

omit h D in
/-- A morphism of a category fibred in groupoids lying over an isomorphism is an isomorphism. -/
theorem isIso_of_isFiberedInGroupoids_of_isIso_map {𝒮 : Type*} {𝒞 : Type*} [Category* 𝒮]
    [Category* 𝒞] (p : 𝒮 ⥤ 𝒞) (hp : p.IsFiberedInGroupoids) {a b : 𝒮} (φ : a ⟶ b)
    [IsIso (p.map φ)] : IsIso φ := by
  have : p.IsStronglyCartesian (p.map φ) φ :=
    Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift hp (p.map φ) φ
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso p (p.map φ) φ

/-- **The transport functor is an equivalence over the site of `S`**: it is fully faithful, lies
over `Over.map h`, and every object of `Coh_{Λ_h X/Λ_h Y}` is vertically isomorphic to a
transport. -/
theorem nonempty_isEquivalenceOver_relocalizeCoherentFunctor :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    letI : Category.{u + 1} (CoherentObject (D.relocalize h)) :=
      (D.relocalize h).categoryData.category
    Nonempty (IsEquivalenceOver (coherentSiteProjection D.categoryData ⋙ Over.map h)
      (coherentSiteProjection (D.relocalize h).categoryData) (D.relocalizeCoherentFunctor h)) := by
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  let : Category.{u + 1} (CoherentObject (D.relocalize h)) :=
    (D.relocalize h).categoryData.category
  have : (D.relocalizeCoherentFunctor h).Full := D.relocalizeCoherentFunctor_full h
  have : (D.relocalizeCoherentFunctor h).Faithful := D.relocalizeCoherentFunctor_faithful h
  refine nonempty_isEquivalenceOver_of_forall_verticalObjPreimage _ _ _
    (D.relocalizeCoherentFunctor_comp_projection h) fun y => ?_
  let φ : y ⟶ (D.relocalizeCoherentFunctor h).obj (D.descendObject h y) := D.descendHom h y
  have hφ : (coherentSiteProjection (D.relocalize h).categoryData).map φ =
      eqToHom (D.relocalizeTest_descendTest_left h y.T).symm :=
    D.descendTestIso_inv_left h y.T
  have : IsIso ((coherentSiteProjection (D.relocalize h).categoryData).map φ) := by
    rw [hφ]
    exact (eqToIso (D.relocalizeTest_descendTest_left h y.T).symm).isIso_hom
  have : IsIso φ := isIso_of_isFiberedInGroupoids_of_isIso_map _
    (D.relocalize h).isFiberedInGroupoids_siteProjection φ
  exact ⟨D.descendObject h y, D.relocalizeTest_descendTest_left h y.T, asIso φ, hφ⟩

/-- **`Coh_{X/Y}`, read over `S` through `h`, is equivalent over the site of `S` to
`Coh_{Λ_h X/Λ_h Y}`.** -/
def relocalizeEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver (D.coherentCFG.val.p ⋙ Over.map h)
      (D.relocalize h).coherentCFG.val.p :=
  letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  letI : Category.{u + 1} (CoherentObject (D.relocalize h)) :=
    (D.relocalize h).categoryData.category
  StacksRepresentableCFG.EquivalenceOver.ofIsEquivalenceOver
    (D.nonempty_isEquivalenceOver_relocalizeCoherentFunctor h).some

/-- **Algebraicity of `Coh_{X/Y}` over `W` follows from algebraicity of `Coh_{Λ_h X/Λ_h Y}` over
`S`**: the latter is equivalent to `Coh_{X/Y}` viewed over `S` (Construction A of Stacks 04WT),
and an algebraic stack over `S` produced by Construction A comes from an algebraic stack over
`W` (Stacks 04X5). The morphisms of `Coh_{X/Y}` lie in the universe `u + 1`; the change of base
is run on the version with hom-sets shrunk to `u`, which is locally small because the transport
functor is faithful into a locally small category. -/
theorem isAlgebraicStack_of_relocalize.{w}
    (H : Stack.IsAlgebraicStack.{u, w} B S hS (D.relocalize h).coherentCFG.val) :
    Stack.IsAlgebraicStack.{u, w} B W hW D.coherentCFG.val := by
  have : LocallySmall.{u} (D.relocalize h).coherentCFG.val.obj :=
    Stack.locallySmall_of_isAlgebraicStack B S hS H
  have : LocallySmall.{u} D.coherentCFG.val.obj := by
    let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    let : Category.{u + 1} (CoherentObject (D.relocalize h)) :=
      (D.relocalize h).categoryData.category
    exact @locallySmall_of_faithful _ _ _ _ (D.relocalizeCoherentFunctor h)
      (D.relocalizeCoherentFunctor_faithful h) (Stack.locallySmall_of_isAlgebraicStack B S hS H)
  let 𝒴 := Stack.shrinkHomsCFG B W hW D.coherentCFG
  have h₁ : Stack.IsAlgebraicStack.{u, w} B S hS (Stack.changeBase B W S hW hS h 𝒴.val) :=
    Stack.isAlgebraicStack_of_equivalenceOver B S hS
      ((D.relocalizeEquivalenceOver h).symm.trans
        (StacksRepresentableCFG.shrinkHomsEquivalenceOver.{u}
          (D.coherentCFG.val.p ⋙ Over.map h))) H
  have h₂ : Stack.IsAlgebraicStack.{u, w} B W hW 𝒴.val :=
    Stack.isAlgebraicStack_of_changeBase B W S hW hS h 𝒴 h₁
  exact Stack.isAlgebraicStack_of_equivalenceOver B W hW
    (StacksRepresentableCFG.shrinkHomsEquivalenceOver.{u} D.coherentCFG.val.p).symm h₂


/-! ### Replacing the base scheme by `Spec ℤ` -/

omit h D in
/-- **Stacks 09DS from its inputs over `Spec ℤ`.** Let `f : X ⟶ Y` be a separated morphism of
finite presentation of algebraic spaces over an arbitrary scheme `S` of the site. If every `Coh`
over `Spec ℤ` has representable diagonal (Stacks 08W6) and, for every separated standing datum over
`Spec ℤ` whose base is a coproduct of affine schemes, locally of finite presentation over `ℤ`,
`Coh` has finite-dimensional tangent spaces (Stacks 08W8), effective formal objects (Stacks 08W9)
and satisfies Grothendieck's existence theorem on towers of thickenings (Stacks 0CXB, read on
`Coh` as `AlgebraicGeometry.Space.CoherentSituation.TowerExistence`), then `Coh_{X/Y}` is an
algebraic stack over `S`.

The reduction is the lower-shriek extension along `S ⟶ Spec ℤ`
(`AlgebraicGeometry.Space.CoherentSituation.isAlgebraicStack_of_relocalize`), followed by the
reduction over `Spec ℤ` of
`AlgebraicGeometry.Space.isAlgebraicStack_overIntegers_of_artinInputs`, whose size condition [-1]
is `AlgebraicGeometry.Space.CoherentSituation.isSizeBounded_coherentCFG_overIntegers`. -/
theorem isAlgebraicStack_of_artinInputs_overIntegers.{w} {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} (D : CoherentSituation B S hS) (hsep : IsSeparated B S hS D.f.hom)
    (hdiag : ∀ D : CoherentSituation B (⊤_ Scheme.{u}) B.contains_terminal,
      Stack.HasRepresentableDiagonal B _ B.contains_terminal D.coherentCFG)
    (hinputs : ∀ (V₀ : BigFppfOver B (⊤_ Scheme.{u}) B.contains_terminal),
      LocallyOfFinitePresentation (B.inclusion.map V₀.hom) → IsCoproductOfAffines V₀ →
      ∀ (D₀ : CoherentSituation B (⊤_ Scheme.{u}) B.contains_terminal),
        D₀.Y = (schemeSpaceFunctor B _ B.contains_terminal).obj V₀ →
        IsSeparated B _ B.contains_terminal D₀.f.hom →
        Stack.HasFiniteDimensionalTangentSpaces B _ B.contains_terminal D₀.coherentCFG ∧
        (∀ ξ : Deformation.Artin.FormalObject B _ B.contains_terminal D₀.coherentCFG.val.p,
          Deformation.Artin.FormalObject.IsEffective B _ B.contains_terminal D₀.coherentCFG.val.p
            D₀.coherentCFG.property ξ) ∧
        D₀.TowerExistence) :
    Stack.IsAlgebraicStack.{u, w} B S hS D.coherentCFG.val := by
  let g : B.obj hS ⟶ B.obj B.contains_terminal := ⟨terminal.from S⟩
  exact D.isAlgebraicStack_of_relocalize g
    (isAlgebraicStack_overIntegers_of_artinInputs B.contains_terminal (D.relocalize g)
      (D.isSeparated_relocalize g hsep) hdiag fun V₀ hV₀ hV₀c D₀ hY hsep₀ =>
        have h := hinputs V₀ hV₀ hV₀c D₀ hY hsep₀
        ⟨D₀.isSizeBounded_coherentCFG_overIntegers hsep₀ V₀ hY, h.1, h.2.1,
          D₀.isSquareZeroEffective_of_towerExistence V₀ hY hV₀c h.2.2⟩)

end AlgebraicGeometry.Space.CoherentSituation

end
