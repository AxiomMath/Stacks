module

public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.AffineRightAdjoint
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.ParasiticLisseEtaleVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionFlatProjections
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import all StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Representable

/-!
# The counit of an affine 1-morphism lies over a base change

Let `g : 𝒰 ⟶ 𝒳` be an affine 1-morphism of algebraic stacks and `r : 𝒳 ⥤ 𝒰` its right adjoint
(`AlgebraicGeometry.Stack.affineRightAdjoint`).  At an object `x` of `𝒳` lying over a scheme
`T`, the counit `g (r x) ⟶ x` lies over the projection `W_x = 𝒰 ×_𝒳 T ⟶ T`, the scheme
representing the base change of `g` along `x`.  So every property of morphisms of algebraic
spaces that `g` has in the relative sense of Stacks 03YK is a property of that projection.  This
file records it for flatness (Stacks 06PW) and surjectivity (Stacks 04ZS): if `g` is flat, resp.
surjective, then the counit lies over a flat, resp. surjective, morphism of schemes.

## Main results

* `AlgebraicGeometry.Stack.prop_yoneda_map_of_prop_algebraicSpaceMap`: a property of the
  structural morphism of an algebraic space over `T` represented by a scheme `Z` over `T` is a
  property of the morphism of representable presheaves `Z ⟶ T`.
* `AlgebraicGeometry.BigFppfOver.exists_isTerminal_costructuredArrow_of_hasRelativeProperty`:
  the comma categories of an affine 1-morphism with a relative property `P` have terminal
  objects lying over morphisms of schemes with the corresponding property.
* `AlgebraicGeometry.Stack.flat_map_affineAdjunction_counit`,
  `AlgebraicGeometry.Stack.surjective_map_affineAdjunction_counit`: the counit of a flat,
  resp. surjective, affine 1-morphism lies over a flat, resp. surjective, morphism of schemes.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04ZS](https://stacks.math.columbia.edu/tag/04ZS)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A property of the structural morphism of an algebraic space represented by a scheme is a
property of the representing morphism.**  Let `A` be an algebraic space over `T` represented on
the big fppf site of `T` by `Z`.  If the structural morphism of `A`, read as a morphism of
algebraic spaces over `S`, has an isomorphism-invariant property `P`, then so does the morphism
of representable presheaves induced by `Z ⟶ T`. -/
theorem prop_yoneda_map_of_prop_algebraicSpaceMap
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.RespectsIso]
    (T : BigFppfOver B S hS) (A : (BigFppfOver B T.left.1 T.left.2)ᵒᵖ ⥤ Type u)
    (hA : IsAlgebraicSpace B T.left.1 T.left.2 A) (Z : BigFppfOver B T.left.1 T.left.2)
    (e : A ≅ yoneda.obj Z)
    (h : P (algebraicSpaceMap B S hS T
      ((spacesOverSmallerBaseFunctor B T.left.1 S T.left.2 hS T.hom).obj ⟨A, hA⟩))) :
    P (ObjectProperty.homMk (yoneda.map ((Over.iteratedSliceBackward (Over.mk T.hom)).obj Z).hom) :
      (schemeSpace _ : AlgebraicSpaces B S hS) ⟶
        schemeSpace _) := by
  let E := smallerBasePresheafEquivalence B T.left.1 S T.left.2 hS T.hom
  let Pz := ((Over.iteratedSliceBackward (Over.mk T.hom)).obj Z).hom
  let i : A ≅ E.inverse.obj (Over.mk (yoneda.map Pz)) :=
    e ≪≫ (fiberYonedaMapIso B S hS T Pz).symm
  let j : E.functor.obj A ≅ Over.mk (yoneda.map Pz) :=
    E.functor.mapIso i ≪≫ E.counitIso.app _
  have hw : j.hom.left ≫ yoneda.map Pz = (E.functor.obj A).hom := Over.w j.hom
  let J : (⟨(E.functor.obj A).left,
      ((spacesOverSmallerBaseFunctor B T.left.1 S T.left.2 hS T.hom).obj ⟨A, hA⟩).property⟩ :
        AlgebraicSpaces B S hS) ≅ ⟨yoneda.obj _, isAlgebraicSpace_yoneda B S hS _⟩ :=
    ObjectProperty.isoMk _ ((Over.forget _).mapIso j)
  have hJ : J.hom ≫ (ObjectProperty.homMk (yoneda.map Pz) :
      (⟨yoneda.obj _, isAlgebraicSpace_yoneda B S hS _⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨yoneda.obj _, isAlgebraicSpace_yoneda B S hS _⟩) =
      algebraicSpaceMap B S hS T
        ((spacesOverSmallerBaseFunctor B T.left.1 S T.left.2 hS T.hom).obj ⟨A, hA⟩) := by
    ext1
    exact hw
  rw [← hJ] at h
  exact (P.cancel_left_of_respectsIso J.hom _).1 h

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The 2-fibre product of an affine 1-morphism with a scheme-valued point has a terminal
object lying over a morphism of schemes with every relative property of the 1-morphism.**  Let
`P` be a property of morphisms of algebraic spaces which `g` has in the sense of Stacks 03YK, and
`Q` an isomorphism-invariant property of morphisms of schemes that `P` implies on morphisms of
representable presheaves.  Then the terminal object of `𝒰 ×_𝒳 (Sch/T)` lies over a morphism of
schemes to `T` with `Q`. -/
theorem exists_isTerminal_twoFibreProductOver_of_hasRelativeProperty
    {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS}
    (g : 𝒰 ⟶ 𝒳) (hg : AlgebraicStacks.IsAffineHom B S hS g)
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    (hP : HasRelativeProperty B S hS P g.hom hg.1)
    (Q : MorphismProperty Scheme.{u})
    (hPQ : ∀ {V W : BigFppfOver B S hS} (k : V ⟶ W), P (ObjectProperty.homMk (yoneda.map k) :
      (schemeSpace V : AlgebraicSpaces B S hS) ⟶
        schemeSpace W) →
      Q ((BigFppfOver.toScheme B S hS).map k))
    (T : BigFppfOver B S hS) (G : Over T ⥤ 𝒳.val.val.obj) (hG : G ⋙ 𝒳.val.val.p = Over.forget T) :
    ∃ Q' : TwoFibreProductOver (Over.forget T) 𝒰.val.val.p 𝒳.val.val.p G g.hom.hom.toFunctor,
      Nonempty (IsTerminal Q') ∧ Q ((BigFppfOver.toScheme B S hS).map Q'.x.hom) := by
  have hy : (Over.iteratedSliceBackward T ⋙ G) ⋙ 𝒳.val.val.p = Over.map T.hom := by
    rw [Functor.assoc, hG]
    exact Over.iteratedSliceBackward_forget T
  obtain ⟨A, hA, ⟨e⟩⟩ := hg.1 T _ hy
  obtain ⟨Y, Pm, ⟨iA⟩, -⟩ :=
    exists_iso_yoneda_of_isAffineHom_algebraicSpaceMap B S hS T A hA (hg.2 T _ hy A hA ⟨e⟩)
  let V0 := (Over.iteratedSliceForward (Over.mk T.hom)).obj (Over.mk Pm)
  have hQ : Q ((BigFppfOver.toScheme B S hS).map
      ((Over.iteratedSliceBackward (Over.mk T.hom)).obj V0).hom) :=
    hPQ _ (prop_yoneda_map_of_prop_algebraicSpaceMap B S hS P T A hA V0 iA (hP T _ hy A hA ⟨e⟩))
  let e' := (e.trans (PresheafOfCategories.equivalenceOverOfIso iA)).trans
    (PresheafOfCategories.sliceElementsEquivalenceOver V0).symm
  let Q0 := e'.toEquivalence.inverse.obj (Over.mk (𝟙 V0))
  have hQ0 : IsTerminal Q0 := IsTerminal.isTerminalObj _ _ Over.mkIdTerminal
  have hx0 : Q0.x = V0 := Functor.congr_obj e'.inv.w (Over.mk (𝟙 V0))
  have hΦ := TwoFibreProductOver.isEquivalence_precomposeFst (Over.map T.hom) (Over.forget T)
    𝒰.val.val.p 𝒳.val.val.p G g.hom.hom.toFunctor (Over.iteratedSliceBackward T) rfl
    𝒰.val.isFiberedInGroupoids (Functor.IsFiberedInGroupoids.over_map T.hom)
    (Functor.IsFiberedInGroupoids.over_forget T) (Over.iteratedSliceEquiv T).isEquivalence_inverse
    hG
  refine ⟨(TwoFibreProductOver.precomposeFst (Over.map T.hom) (Over.forget T)
    𝒰.val.val.p 𝒳.val.val.p G g.hom.hom.toFunctor (Over.iteratedSliceBackward T) rfl).obj Q0,
    ⟨IsTerminal.isTerminalObj _ _ hQ0⟩, ?_⟩
  have key : ∀ (Z : Over T.left) (_ : Z = V0), Q
      ((BigFppfOver.toScheme B S hS).map ((Over.iteratedSliceBackward T).obj Z).hom) := by
    rintro _ rfl
    exact hQ
  exact key _ hx0

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.BigFppfOver
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

open Functor.ChoiceOfPullbacks in
/-- **The comma categories of an affine 1-morphism with a relative property `P` have terminal
objects lying over morphisms of schemes with the corresponding property `Q`.**  This is
`AlgebraicGeometry.BigFppfOver.exists_isTerminal_costructuredArrow_of_isAffineHom` with an
arbitrary isomorphism-invariant property of morphisms of schemes in place of affineness. -/
theorem exists_isTerminal_costructuredArrow_of_hasRelativeProperty
    {𝒰 𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}
    (g : 𝒰 ⟶ 𝒳) (hg : Stack.AlgebraicStacks.IsAffineHom B S hS g)
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    (hP : Stack.HasRelativeProperty B S hS P g.hom hg.1)
    (Q : MorphismProperty Scheme.{u}) [Q.RespectsIso]
    (hPQ : ∀ {V W : BigFppfOver B S hS} (k : V ⟶ W), P (ObjectProperty.homMk (yoneda.map k) :
      (schemeSpace V : AlgebraicSpaces B S hS) ⟶
        schemeSpace W) →
      Q ((BigFppfOver.toScheme B S hS).map k))
    (x : 𝒳.val.val.obj) :
    ∃ c : CostructuredArrow g.hom.hom.toFunctor x, Nonempty (IsTerminal c) ∧
      Q ((BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map c.hom)) := by
  have h𝒳 := 𝒳.val.isFiberedInGroupoids
  have hF : g.hom.hom.toFunctor ⋙ 𝒳.val.val.p = 𝒰.val.val.p := g.hom.hom.w
  obtain ⟨G, hG, ξ, -⟩ := Stacks.RepresentableMorphism.ClassifyingFunctor.exists_classifying_functor
    𝒳.val.val.p h𝒳 (𝒳.val.val.p.obj x) x rfl
  obtain ⟨Q', ⟨hQ⟩, hQ'⟩ :=
    Stack.exists_isTerminal_twoFibreProductOver_of_hasRelativeProperty B S hS g hg P hP Q hPQ _ G hG
  refine ⟨CostructuredArrow.mk (pairMorphism Q' ≫ ξ.hom), ⟨?_⟩, ?_⟩
  · refine IsTerminal.ofUniqueHom (fun c => CostructuredArrow.homMk
      (hQ.from (pairOfMorphism hF hG h𝒳 c.left (c.hom ≫ ξ.inv))).b ?_) ?_
    · change g.hom.hom.toFunctor.map _ ≫ pairMorphism Q' ≫ ξ.hom = c.hom
      rw [← Category.assoc,
        pairMorphism_naturality (hQ.from (pairOfMorphism hF hG h𝒳 c.left (c.hom ≫ ξ.inv))),
        pairMorphism_pairOfMorphism hF hG h𝒳 c.left (c.hom ≫ ξ.inv), Category.assoc,
        Iso.inv_hom_id, Category.comp_id]
    · intro c m
      have h2 := pairMorphism_pairOfMorphism hF hG h𝒳 c.left (c.hom ≫ ξ.inv)
      have hw : g.hom.hom.toFunctor.map m.left ≫ pairMorphism Q' ≫ ξ.hom = c.hom :=
        CostructuredArrow.w m
      have hm : g.hom.hom.toFunctor.map m.left ≫ pairMorphism Q' =
          pairMorphism (pairOfMorphism hF hG h𝒳 c.left (c.hom ≫ ξ.inv)) := by
        rw [h2, ← hw]
        simp
      ext
      exact congrArg TwoFibreProductOver.Hom.b
        (hQ.hom_ext (homOfPairMorphism hF hG h𝒳
          (P := pairOfMorphism hF hG h𝒳 c.left (c.hom ≫ ξ.inv)) (Q := Q') m.left hm) _)
  · change Q ((BigFppfOver.toScheme B S hS).map
      (𝒳.val.val.p.map ((Q'.iso.inv ≫ G.map (toTerminal Q'.x)) ≫ ξ.hom)))
    simp only [Functor.map_comp, map_over hG (toTerminal Q'.x), Category.assoc]
    rwa [Q.cancel_left_of_respectsIso, Q.cancel_left_of_respectsIso,
      Q.cancel_right_of_respectsIso]

end AlgebraicGeometry.BigFppfOver

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (g : 𝒰 ⟶ 𝒳)
  (hg : AlgebraicStacks.IsAffineHom B S hS g)

omit hg in
/-- Lying over a morphism of schemes with an isomorphism-invariant property is invariant under
isomorphism of costructured arrows. -/
theorem prop_toScheme_map_hom_of_iso {C D : Type*} [Category C] [Category D]
    (Pr : D ⥤ BigFppfOver B S hS) {G : C ⥤ D} {x : D} (Q : MorphismProperty Scheme.{u})
    [Q.RespectsIso] {c c' : CostructuredArrow G x} (e : c ≅ c')
    (h : Q ((BigFppfOver.toScheme B S hS).map (Pr.map c'.hom))) :
    Q ((BigFppfOver.toScheme B S hS).map (Pr.map c.hom)) := by
  have : IsIso e.hom.left := (CostructuredArrow.proj _ _).map_isIso e.hom
  rwa [← CostructuredArrow.w e.hom, Functor.map_comp, Functor.map_comp,
    Q.cancel_left_of_respectsIso]

/-- **The counit of an affine 1-morphism with a relative property `P` lies over a morphism of
schemes with the corresponding property `Q`**: at `x` over `T` it lies over the projection
`𝒰 ×_𝒳 T ⟶ T`. -/
theorem prop_map_affineAdjunction_counit
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    (hP : HasRelativeProperty B S hS P g.hom hg.1)
    (Q : MorphismProperty Scheme.{u}) [Q.RespectsIso]
    (hPQ : ∀ {V W : BigFppfOver B S hS} (k : V ⟶ W), P (ObjectProperty.homMk (yoneda.map k) :
      (schemeSpace V : AlgebraicSpaces B S hS) ⟶
        schemeSpace W) →
      Q ((BigFppfOver.toScheme B S hS).map k))
    (x : 𝒳.val.val.obj) :
    Q ((BigFppfOver.toScheme B S hS).map
      (𝒳.val.val.p.map ((affineAdjunction g hg).counit.app x))) := by
  obtain ⟨c, ⟨hc⟩, hcQ⟩ := BigFppfOver.exists_isTerminal_costructuredArrow_of_hasRelativeProperty
    B S hS g hg P hP Q hPQ x
  exact prop_toScheme_map_hom_of_iso 𝒳.val.val.p Q
    (IsTerminal.uniqueUpToIso (mkTerminalOfRightAdjoint (h := affineAdjunction g hg) (A := x)) hc)
    hcQ

/-- **The counit of a flat affine 1-morphism lies over a flat morphism of schemes**: at `x` over
`T`, the projection `𝒰 ×_𝒳 T ⟶ T` is the base change of `g`, hence flat (Stacks 06PW). -/
theorem flat_map_affineAdjunction_counit (hflat : AlgebraicStacks.IsFlat B S hS g)
    (x : 𝒳.val.val.obj) :
    AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map
      (𝒳.val.val.p.map ((affineAdjunction g hg).counit.app x))) := by
  have hbc : (spaceProperty B S hS (fun _ _ h => Space.IsFlat B S hS h)).IsStableUnderBaseChange :=
    Space.isFlat_isStableUnderBaseChange B S hS
  have hlt : (spaceProperty B S hS (fun _ _ h => Space.IsFlat B S hS h)).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isFlat_isLocalAtTarget_fppf B S hS
  have hrel : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (spaceProperty B S hS (fun _ _ h => Space.IsFlat B S hS h)) g.hom hg.1 :=
    hasRelativeProperty_of_hasPropertyOnSomeSmoothDiagram B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) g.hom hg.1
      ((AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS g).1 hflat)
  have hFbc : MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u}) :=
    AlgebraicGeometry.Flat.isStableUnderBaseChange
  have : MorphismProperty.RespectsIso (@AlgebraicGeometry.Flat.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact prop_map_affineAdjunction_counit g hg _ hrel @AlgebraicGeometry.Flat.{u}
    (fun k hk => (isFlat_yoneda_map_iff B S hS k).1 hk) x

/-- **The counit of a surjective affine 1-morphism lies over a surjective morphism of
schemes**: at `x` over `T`, the projection `𝒰 ×_𝒳 T ⟶ T` is the base change of `g`, hence
surjective (Stacks 04ZS). -/
theorem surjective_map_affineAdjunction_counit (hsurj : IsSurjective B S hS g)
    (x : 𝒳.val.val.obj) :
    AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map
      (𝒳.val.val.p.map ((affineAdjunction g hg).counit.app x))) := by
  have hrel : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.surjectiveMorphismProperty B S hS)
      g.hom hg.1 :=
    (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS g hg.1).1 hsurj
  have hstab : MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) :=
    inferInstance
  exact prop_map_affineAdjunction_counit g hg _ hrel @AlgebraicGeometry.Surjective.{u}
    (fun k hk => (Space.presheaf_yoneda_map_iff B S hS hstab k).1
      ((Space.surjective_yonedaMap_iff_surjective_pointsMap B S hS k).2 hk)) x

end AlgebraicGeometry.Stack

end
