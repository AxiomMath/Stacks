module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSiteLocalization
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafFunctoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Modules
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels

/-!
# Pullback preserves quasi-coherent modules on a fibred category (Stacks 06WH)

Let `f : 𝒳 ⥤ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf category of
a scheme `S`. Stacks 06WH says the inverse image `f^* = f^{-1}` of sheaves of modules
(Stacks 06WE) carries quasi-coherent sheaves to quasi-coherent sheaves.

Quasi-coherence is `SheafOfModules.IsQuasicoherentOnSite`, the local-presentation form of
Stacks 03DL(6): every object of the site has a covering on whose members the module is the
cokernel of a map between coproducts of copies of the structure sheaf.

The proof is in two steps, the first of which is general site theory and is given here for an
arbitrary continuous functor. Restricting a sheaf of modules along a continuous functor `F`
whose slices `Over U ⥤ Over (F.obj U)` are equivalences preserves quasi-coherence: a covering
of `F.obj U` on which the module is globally presented pulls back, using cocontinuity of `F`, to
a covering of `U`, and on each member the restriction functor is an equivalence of slices, hence
has a left adjoint and so preserves the coproducts and the cokernel of the presentation. The
second step identifies the inverse image of Stacks 06WE with that restriction and checks that
`f` has the slice property, which is exactly Stacks 06W0.

## Main definitions

* `SheafOfModules.restrictAlongContinuous`: the restriction of sheaves of modules along a
  continuous functor, with scalars restricted along the same functor.

## Main results

* `CategoryTheory.Adjunction.whiskerLeft_op_triangle`: the triangle identity of an adjunction,
  read on the restrictions of a presheaf on the target.
* `SheafOfModules.isLeftAdjoint_restrictAlongContinuous`: that restriction has a left adjoint
  when the functor does, so it preserves colimits.
* `SheafOfModules.hasGlobalPresentation_restrictAlongContinuous` and
  `SheafOfModules.isQuasicoherentOnSite_restrictAlongContinuous`: restriction preserves global
  presentations, and preserves quasi-coherence when the slices of the functor are equivalences.
* `SheafOfModules.isQuasicoherentOnSite_of_restrictionIso`: a sheaf of modules isomorphic, as a
  presheaf of modules with restricted scalars, to such a restriction is quasi-coherent.
* `AlgebraicGeometry.Stack.isQuasicoherentOnSite_modulePullback`: **Stacks 06WH**.

## Implementation notes

The slice hypothesis is `∀ U, (CategoryTheory.Over.post F).IsEquivalence` rather than an
equivalence of the whole categories, because that is what Stacks 06W0 provides for a
1-morphism of categories fibred in groupoids and it is all the local argument uses.

Transport of quasi-coherence along an isomorphism is
`SheafOfModules.IsQuasicoherentOnSite.of_iso`, already available, so the last step is a change
of scalars and not a second local argument. The identification of the two structure presheaves
is an equality of presheaves of rings, so it is a `CategoryTheory.eqToHom` and the two sheaves
of rings are equal by `CategoryTheory.ObjectProperty.FullSubcategory.ext`.

## References

* [Stacks Project, Tag 06WH](https://stacks.math.columbia.edu/tag/06WH)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w m

namespace CategoryTheory.Adjunction

/-- The triangle identity of an adjunction `F ⊣ G`, read on the restrictions of a presheaf `P`
on the target: the unit of the induced adjunction on presheaves, restricted along `F.op` and
followed by the action of the unit of `F ⊣ G` on `F.op ⋙ P`, is the identity.

This is the second compatibility that
`CategoryTheory.SheafOfModules.pushforwardPushforwardAdj` asks for, stated for a presheaf and
with the unit written out, so that it can be proved before either side is read as a morphism of
sheaves of rings. -/
theorem whiskerLeft_op_triangle {C : Type v} [Category.{w} C] {D : Type v} [Category.{w} D]
    {A : Type u} [Category.{m} A] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (P : Dᵒᵖ ⥤ A) :
    𝟙 (F.op ⋙ P) ≫ Functor.whiskerLeft F.op
        (P.leftUnitor.inv ≫ Functor.whiskerRight (NatTrans.op adj.counit) P ≫
          (Functor.associator G.op F.op P).hom) ≫
      Functor.whiskerRight (NatTrans.op adj.unit) (F.op ⋙ P) = 𝟙 (F.op ⋙ P) := by
  ext U
  simp [← P.map_comp, ← op_comp]

end CategoryTheory.Adjunction

namespace SheafOfModules

variable {C D : Type v} [Category.{w} C] [Category.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{u})

/-- The restriction of sheaves of modules along a continuous functor `F`: the underlying
abelian presheaf is precomposed with `F.op`, and the scalars are the restriction of the sheaf of
rings along the same functor, so no change of scalars is needed. -/
noncomputable abbrev restrictAlongContinuous :
    SheafOfModules.{m} R ⥤
      SheafOfModules.{m} ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R) :=
  SheafOfModules.pushforward.{m} (𝟙 ((F.sheafPushforwardContinuous RingCat.{u} J K).obj R))

/-- Restriction of sheaves of modules along a continuous functor with a left adjoint has itself
a left adjoint, namely restriction along that left adjoint; in particular it preserves all
colimits. -/
theorem isLeftAdjoint_restrictAlongContinuous [F.IsCocontinuous J K] [F.IsLeftAdjoint] :
    (restrictAlongContinuous (J := J) F R : SheafOfModules.{m} R ⥤ _).IsLeftAdjoint := by
  let adj := Adjunction.ofIsLeftAdjoint F
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{u}) J K
  let ψ := shAdj.unit.app R
  refine (SheafOfModules.pushforwardPushforwardAdj adj (𝟙 _) ψ ?_ ?_).isLeftAdjoint
  · refine Eq.trans ?_ (Category.comp_id ψ.hom).symm
    simp only [ψ, shAdj, Adjunction.sheafPushforwardContinuous, Adjunction.whiskerLeft]
    ext U : 2
    simp
  · exact Adjunction.whiskerLeft_op_triangle adj R.obj

/-- Restriction along a continuous functor with a left adjoint preserves global presentations:
being a left adjoint it preserves the coproducts and the cokernel that make up the
presentation. -/
theorem hasGlobalPresentation_restrictAlongContinuous [F.IsCocontinuous J K]
    [F.IsLeftAdjoint] (M : SheafOfModules.{max u v w m} R) (hM : M.HasGlobalPresentation) :
    ((restrictAlongContinuous (J := J) F R).obj M).HasGlobalPresentation := by
  let L : SheafOfModules.{max u v w m} R ⥤ _ := restrictAlongContinuous (J := J) F R
  have : L.IsLeftAdjoint := isLeftAdjoint_restrictAlongContinuous F R
  obtain ⟨I, H, P, Q, ι, κ, ⟨hP⟩, ⟨hQ⟩, a, b, hab, ⟨hb⟩⟩ := hM
  refine ⟨I, H, L.obj P, L.obj Q, (fun i ↦ L.map (ι i)),
    (fun i ↦ L.map (κ i)), ⟨isColimitCofanMkObjOfIsColimit L _ _ hP⟩,
    ⟨isColimitCofanMkObjOfIsColimit L _ _ hQ⟩,
    L.map a, L.map b, (L.map_comp a b).symm.trans (congrArg L.map hab), ?_⟩
  exact ⟨isColimitCoforkMapOfIsColimit' L hab hb⟩

/-- Restriction along a continuous and cocontinuous functor whose slice functors are
equivalences preserves quasi-coherence.

A covering of `F.obj U` on which `M` is globally presented is lifted by cocontinuity to a
covering of `U`; the slice equivalence turns each of its members into an object `A i` of `C`
over `U` whose image is the member, and restriction along the slice functor at `A i` is again a
restriction along a continuous functor with a left adjoint, so it preserves the presentation. -/
theorem isQuasicoherentOnSite_restrictAlongContinuous [F.IsCocontinuous J K]
    (hF : ∀ U : C, (Over.post (X := U) F).IsEquivalence)
    (M : SheafOfModules.{max u v w m} R) [M.IsQuasicoherentOnSite] :
    ((restrictAlongContinuous (J := J) F R).obj M).IsQuasicoherentOnSite := by
  constructor
  intro U
  obtain ⟨I, V, f, hf, hV⟩ :=
    SheafOfModules.IsQuasicoherentOnSite.locally_hasGlobalPresentation (M := M) (F.obj U)
  have := hF U
  let E := (Over.post (X := U) F).asEquivalence
  let A (i : I) : Over U := E.inverse.obj (Over.mk (f i))
  let e (i : I) : (Over.post F).obj (A i) ≅ Over.mk (f i) := E.counitIso.app _
  refine ⟨I, (fun i ↦ (A i).left), (fun i ↦ (A i).hom), ?_, ?_⟩
  · apply J.superset_covering _ (F.cover_lift J K hf)
    intro W a ha
    obtain ⟨i, b, he⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp ha
    let k : (Over.post F).obj (Over.mk a) ⟶ (Over.post F).obj (A i) :=
      Over.homMk (V := Over.mk (f i)) b he.symm ≫ (e i).inv
    let l : Over.mk a ⟶ A i := (Over.post F).preimage k
    exact (Sieve.mem_ofArrows_iff _ _ _).mpr ⟨i, l.left, (Over.w l).symm⟩
  · intro i
    let ei : F.obj (A i).left ⟶ V i := (e i).hom.left
    let H : Over (A i).left ⥤ Over (V i) := Over.post F ⋙ Over.map ei
    have := hF (A i).left
    have : (Over.post (X := (A i).left) F).IsContinuous
        (J.over (A i).left) (K.over (F.obj (A i).left)) :=
      Functor.isContinuous_iff_coverPreserving.mpr
        ((CoverPreserving.of_isContinuous F J K).overPost _)
    have : H.IsContinuous (J.over (A i).left) (K.over (V i)) := by
      dsimp only [H]
      infer_instance
    have : H.IsCocontinuous (J.over (A i).left) (K.over (V i)) :=
      isCocontinuous_comp (Over.post F) (Over.map ei)
        (J.over (A i).left) (K.over (F.obj (A i).left))
    have : IsIso ei :=
      inferInstanceAs (IsIso ((Over.forget (F.obj U)).map (e i).hom))
    have : H.IsEquivalence := inferInstance
    exact hasGlobalPresentation_restrictAlongContinuous.{u, max v w, w, m}
      H (R.over (V i)) (M.over (V i)) (hV i)

/-- A sheaf of modules whose underlying presheaf of modules is isomorphic to the restriction
along `F` of a quasi-coherent sheaf of modules, with scalars transported along the equality of
the two structure presheaves, is itself quasi-coherent. -/
theorem isQuasicoherentOnSite_of_restrictionIso
    (T : Sheaf J RingCat.{u}) (hT : T.obj = F.op ⋙ R.obj)
    (M : SheafOfModules.{m} R) (N : SheafOfModules.{m} T)
    (e : N.val ≅ (PresheafOfModules.pushforward₀ F R.obj ⋙
      PresheafOfModules.restrictScalars (eqToHom hT)).obj M.val)
    [((restrictAlongContinuous (J := J) F R).obj M).IsQuasicoherentOnSite] :
    N.IsQuasicoherentOnSite := by
  have hs : T = (F.sheafPushforwardContinuous RingCat.{u} J K).obj R :=
    ObjectProperty.FullSubcategory.ext hT
  subst T
  let e' : N ≅ (restrictAlongContinuous (J := J) F R).obj M :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso e
  exact IsQuasicoherentOnSite.of_iso e'.symm ‹_›

end SheafOfModules

namespace AlgebraicGeometry.Stack

/-- **Stacks 06WH.** The inverse image of sheaves of modules along a 1-morphism of categories
fibred in groupoids over the big fppf category of `S` preserves quasi-coherence.

The inverse image is `AlgebraicGeometry.Stack.modulePullback`, which on underlying presheaves of
modules is restriction along the 1-morphism followed by the change of scalars identifying the
two structure presheaves; and the slices of a 1-morphism of categories fibred in groupoids are
equivalences by Stacks 06W0. -/
@[stacks 06WH]
instance isQuasicoherentOnSite_modulePullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Type v} [Category.{w} 𝒳] [Category.{w} 𝒴]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)
    (M : SheafOfModules.{max u v w m}
      (ringStructureSheafCore B S hS q hq B.topology le_rfl))
    [M.IsQuasicoherentOnSite] :
    ((modulePullback.{u, v, w, max u v w m} B S hS p q hp hq f hf
      B.topology le_rfl).obj M).IsQuasicoherentOnSite := by
  have hF : p.IsFibredOneMorphism q f := hq.isFibredOneMorphism hf
  have : p.IsFibered := hp.isFibered
  have : q.IsFibered := hq.isFibered
  let J := associatedTopology B S hS p B.topology
  let K := associatedTopology B S hS q B.topology
  have : f.IsContinuous J K :=
    (hF.isContinuous_and_isCocontinuous_inheritedTopology (B.topology.over (B.obj hS))).1
  have : f.IsCocontinuous J K :=
    (hF.isContinuous_and_isCocontinuous_inheritedTopology (B.topology.over (B.obj hS))).2
  have hslice : ∀ U : 𝒳, (Over.post (X := U) f).IsEquivalence := by
    intro U
    subst p
    let r := q ⋙ Over.forget (B.obj hS)
    have : (Over.post (X := f.obj U) r).IsEquivalence :=
      isEquivalence_overPost B S hS q hq (f.obj U)
    have : (Over.post (X := U) (f ⋙ r)).IsEquivalence :=
      isEquivalence_overPost B S hS (f ⋙ q) hp U
    have : (Over.post (X := U) f ⋙ Over.post r).IsEquivalence := by
      rw [← Over.post_comp]
      infer_instance
    exact Functor.isEquivalence_of_comp_right (Over.post f) (Over.post r)
  let R := ringStructureSheafCore B S hS q hq B.topology le_rfl
  have : ((SheafOfModules.restrictAlongContinuous (J := J) f R).obj M).IsQuasicoherentOnSite :=
    SheafOfModules.isQuasicoherentOnSite_restrictAlongContinuous.{u, v, w, m} f R hslice M
  let W := moduleSheafFunctoriality.{u, v, w, m, v, w} B S hS p q hp hq f hf
    B.topology le_rfl
  exact SheafOfModules.isQuasicoherentOnSite_of_restrictionIso f R _
    (ringStructureSheafCore_obj_eq B S hS p q hp hq f hf B.topology le_rfl) M
    (W.pullback.obj M) (W.pullback_iso.app M)

end AlgebraicGeometry.Stack

end
