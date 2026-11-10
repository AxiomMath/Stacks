module

public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.RingUniverseLift
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksCore.Tactic.StacksAttribute

/-!
# The largest quasi-coherent submodule of a submodule

Let `X` be an algebraic space over a scheme `S`, let `M` be a quasi-coherent `𝒪_X`-module and
let `G ⊆ M` be an arbitrary `𝒪_X`-submodule.  Stacks 04CK asserts that `G` contains a unique
quasi-coherent `𝒪_X`-submodule `G'` through which every map from a quasi-coherent module into
`G` factors uniquely, and that `G'` is then the largest quasi-coherent submodule of `M`
contained in `G`.

## Main definitions

* `AlgebraicGeometry.Space.IsClosedUnderDirectSumsQuasicoherent` is the direct-sum clause of
  Stacks 03M1 on the small étale ringed site, in the enlarged module universe, stated through
  the universal property of the direct sum so that no cocompleteness instance is assumed.

## Main results

* `AlgebraicGeometry.Space.existsUnique_quasicoherentSubobject_of_closure`: the submodule and
  its universal mapping property.
* `AlgebraicGeometry.Space.exists_greatest_quasicoherentSubobject_of_closure`: its maximality.

## Implementation notes

A submodule is a subobject in the category `AlgebraicGeometry.Space.Modules` of sheaves of
modules on the small étale ringed site, and the universal property is stated as bijectivity of
composition with the subobject arrow, which is exactly the map `Hom(H, G') ⟶ Hom(H, G)` of the
source.  Maximality is stated for subobjects of `G`, so that containment in `G` is part of the
statement rather than an extra clause.

The source proof is the image of the direct sum of *all* quasi-coherent submodules of `G`, so
it quantifies over the subobject lattice of `G`.  That lattice is only small in a universe
containing the small étale site, that is in `max (u + 1) m` and not in the module universe `m`
itself, and the Grothendieck abelian structure of
`Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck`, which is what makes the indexing
type small and the direct sum exist, is likewise only available there.  So the construction is
carried out for the universe lift `SheafOfModules.uliftForPresentation` of the sections and
then brought back down: the resulting subobject of the lift of `G` is replaced by the
pointwise range of its arrow, which is an honest submodule because that arrow is a
monomorphism, and a submodule of the lift of `G` restricts to a submodule of `G`.  Both
transfers preserve quasi-coherence, by
`SheafOfModules.isQuasicoherentOnSite_uliftForPresentation` and
`SheafOfModules.IsQuasicoherentOnSite.of_uliftForPresentation`.  That whole passage between
the two module universes is unconditional, as is the local-membership argument identifying a
monomorphism with the submodule which is its pointwise range.

No `@[stacks 04CK]` tag is carried.  Beyond the universe bookkeeping, the source proof uses
exactly three closure properties of quasi-coherence, and all three appear as hypotheses here
because this tree does not have them unconditionally: closure under kernels and under cokernels,
which is what makes the image of a map of quasi-coherent modules quasi-coherent, and closure
under arbitrary direct sums.  These are the clauses (1) and (3) of Stacks 03M1, whose case of a
scheme is Stacks 0GNB; `StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentFiniteProducts` proves
the finite-product clause.  By the étale localization of the proof of Stacks 03M1 all three reduce
to one statement about the slice of the small étale site at an étale chart with affine underlying
scheme: that a quasi-coherent module there is globally presented, which is the content of Stacks
03DX and rests on Stacks 03DW.  Once that lands, the hypotheses here become instances and both
statements below state Stacks 04CK outright.

The locality step of that reduction is available in the universes this file works in:
`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_coversTop_hasGlobalPresentation`, in
`StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentLocality`, is the clause of Stacks 03DN
for quasi-coherence with the universe of the module sections freed from the universe of the
coefficient rings, which is what the enlarged module universe `max (u + 1) m` here needs.

Two of the three are already carried out, in
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentAffineChartPresentation`, each reduced to the
affine inputs it needs and nothing else.
`AlgebraicGeometry.Space.isClosedUnderDirectSumsQuasicoherent_of_hasAffineChartPresentations`
derives the direct-sum hypothesis `hsum` from
`AlgebraicGeometry.Space.HasAffineChartPresentations`, which is Stacks 03DX for the small étale
ringed site and nothing more; the step that needs no geometry is
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_coversTop_isColimit_cofan`.  And
`AlgebraicGeometry.Space.isClosedUnderCokernels_of_hasAffineChartPresentations` derives the
cokernel instance from that same input together with
`AlgebraicGeometry.Space.HasAffineChartSurjectivePresentations`, which is the vanishing of
Stacks 03DW on an affine chart — surjectivity on sections of a presenting morphism over the
chart, which is what supplies the lift of
`SheafOfModules.HasGlobalPresentation.of_isColimit_cokernelCofork_of_lift`.

The kernel instance is the one clause with no reduction here.  Beyond Stacks 03DX and Stacks 03DW
it needs flat base change of a kernel along an étale morphism of affine charts, the geometric
wrapper of `Module.Descent.isBaseChange_ker`, which this tree does not have.

## References

* [Stacks Project, Tag 04CK](https://stacks.math.columbia.edu/tag/04CK)
* [Stacks Project, Tag 03G9](https://stacks.math.columbia.edu/tag/03G9)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r m t

namespace SheafOfModules

section UniverseLift

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- The pointwise range of a monomorphism of sheaves of modules, as a submodule of its target.

Membership in the pointwise range is already a local condition when the map is a
monomorphism: a covering family of local preimages of a section is compatible, because the
map is sectionwise injective, so it glues to a preimage over the object itself. -/
noncomputable def monoRangeSubmodule {A G : SheafOfModules.{m} R} (f : A ⟶ G)
    [Mono f] : G.Submodule where
  toSubmodule := _root_.Stacks.SheafOfModules.ImageSubsheaf.rangeSubmodule f
  isSheaf := by
    intro U s hs
    set N := _root_.Stacks.SheafOfModules.ImageSubsheaf.rangeSubmodule f
    set T : Sieve U.unop := N.toSubfunctor.sieveOfSection s
    have hpre (V : C) (g : V ⟶ U.unop) (hg : T g) :
        ∃ y, (f.val.app (op V)).hom y = G.val.map g.op s := by
      change G.val.map g.op s ∈ LinearMap.range (f.val.app (op V)).hom at hg
      exact LinearMap.mem_range.mp hg
    set AP := A.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m}
    set GP := G.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m}
    set fam : Presieve.FamilyOfElements AP T.arrows := fun V g hg =>
      Classical.choose (hpre V g hg)
    have hspec (V : C) (g : V ⟶ U.unop) (hg : T.arrows g) :
        f.val.app (op V) (fam g hg) = G.val.map g.op s :=
      Classical.choose_spec (hpre V g hg)
    have hcomp : fam.Compatible := by
      intro V₁ V₂ W g₁ g₂ f₁ f₂ h₁ h₂ hc
      have hmono : Mono ((SheafOfModules.evaluation R (op W)).map f) := inferInstance
      apply (ModuleCat.mono_iff_injective _).mp hmono
      change f.val.app (op W) (A.val.map g₁.op (fam f₁ h₁)) =
        f.val.app (op W) (A.val.map g₂.op (fam f₂ h₂))
      rw [PresheafOfModules.naturality_apply f.val g₁.op (fam f₁ h₁),
        PresheafOfModules.naturality_apply f.val g₂.op (fam f₂ h₂),
        hspec V₁ f₁ h₁, hspec V₂ f₂ h₂,
        ← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply,
        ← op_comp, hc, ← op_comp]
    have hAP : Presheaf.IsSheaf J AP :=
      GrothendieckTopology.HasSheafCompose.isSheaf _ A.isSheaf
    have hGP : Presheaf.IsSheaf J GP :=
      GrothendieckTopology.HasSheafCompose.isSheaf _ G.isSheaf
    have hsh := (isSheaf_iff_isSheaf_of_type J AP).1 hAP T hs
    set y : A.val.obj U := hsh.amalgamate fam hcomp
    refine ⟨y, ?_⟩
    refine ((isSheaf_iff_isSheaf_of_type J GP).1 hGP T hs).isSeparatedFor.ext fun V g hg => ?_
    change G.val.map g.op (f.val.app U y) = G.val.map g.op s
    rw [← PresheafOfModules.naturality_apply f.val g.op y]
    change f.val.app (op V) (A.val.map g.op y) = _
    rw [show A.val.map g.op y = fam g hg from hsh.valid_glue hcomp g hg, hspec V g hg]

/-- A monomorphism of sheaves of modules is an isomorphism onto the submodule which is its
pointwise range. -/
noncomputable def isoMonoRangeSubmodule {A G : SheafOfModules.{m} R} (f : A ⟶ G)
    [Mono f] : A ≅ (monoRangeSubmodule f).toSheafOfModules :=
  (SheafOfModules.fullyFaithfulForget R).preimageIso <|
    PresheafOfModules.isoMk
      (fun U => (LinearEquiv.ofBijective (LinearMap.rangeRestrict (f.val.app U).hom)
        ⟨fun _ _ h => (ModuleCat.mono_iff_injective _).mp
            ((inferInstance : Mono ((SheafOfModules.evaluation R U).map f)))
            (congrArg Subtype.val h),
          fun y => ⟨y.2.choose, Subtype.ext y.2.choose_spec⟩⟩).toModuleIso)
      (by
        intro U V g
        ext x
        exact Subtype.ext (PresheafOfModules.naturality_apply f.val g x))

/-- A submodule of the universe lift of the sections of a sheaf of modules restricts to a
submodule of the sheaf itself: a section belongs to the restriction exactly when its lift
belongs to the given submodule, and the two membership sieves coincide. -/
private noncomputable def submoduleOfUlift {G : SheafOfModules.{m} R}
    (N : (uliftForPresentation.{u, v, r, m, t} G).Submodule) : G.Submodule := by
  set N₀ : PresheafOfModules.Submodule G.val :=
    { obj := fun U => (N.toSubmodule.obj U).comap ULift.moduleEquiv.symm.toLinearMap
      map := by
        intro U V f x hx
        change ULift.up x ∈ N.toSubmodule.obj U at hx
        change ULift.up (G.val.map f x) ∈ N.toSubmodule.obj V
        exact N.toSubmodule.map f hx } with hN₀
  refine { toSubmodule := N₀, isSheaf := ?_ }
  intro U s hs
  refine N.isSheaf (ULift.up s) ?_
  have heq : N₀.toSubfunctor.sieveOfSection s =
      N.toSubmodule.toSubfunctor.sieveOfSection (ULift.up s) := by
    ext V g
    rfl
  exact heq ▸ hs

/-- The universe lift of the sections of the restriction of a submodule along the universe
lift is the submodule itself. -/
private noncomputable def uliftSubmoduleOfUliftIso {G : SheafOfModules.{m} R}
    (N : (uliftForPresentation.{u, v, r, m, t} G).Submodule) :
    uliftForPresentation.{u, v, r, m, t} (submoduleOfUlift N).toSheafOfModules ≅
      N.toSheafOfModules := by
  set D := submoduleOfUlift.{u, v, r, m, t} N
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso (PresheafOfModules.isoMk
    (fun U => ?_) ?_)
  · refine LinearEquiv.toModuleIso
      (e := (?_ : ULift.{t} (D.toSubmodule.obj U) ≃ₗ[R.obj.obj U] N.toSubmodule.obj U))
    exact
      { toFun := fun x => ⟨ULift.up x.down.1, x.down.2⟩
        invFun := fun x => ULift.up ⟨x.1.down, x.2⟩
        left_inv := fun _ => ULift.ext rfl
        right_inv := fun _ => Subtype.ext rfl
        map_add' := fun _ _ => Subtype.ext rfl
        map_smul' := fun _ _ => Subtype.ext rfl }
  · intro U V f
    ext x
    exact Subtype.ext rfl

/-- A map between universe lifts of the sections of sheaves of modules comes from a map of the
sheaves themselves. -/
private noncomputable def mapOfUliftMap {A D : SheafOfModules.{m} R}
    (f : uliftForPresentation.{u, v, r, m, t} A ⟶ uliftForPresentation.{u, v, r, m, t} D) :
    A ⟶ D where
  val :=
    { app := fun U => ModuleCat.ofHom
        { toFun := fun x => (f.val.app U (ULift.up x)).down
          map_add' := fun x y => congrArg ULift.down
            ((f.val.app U).hom.map_add (ULift.up x) (ULift.up y))
          map_smul' := fun a x => congrArg ULift.down
            ((f.val.app U).hom.map_smul a (ULift.up x)) }
      naturality := by
        intro U V g
        ext x
        exact congrArg ULift.down
          (PresheafOfModules.naturality_apply f.val g (ULift.up x)) }

/-- The universe lift of the sections preserves monomorphisms: it is sectionwise injective
exactly when the given map is. -/
private theorem mono_uliftForPresentationMap {A D : SheafOfModules.{m} R} (f : A ⟶ D)
    [Mono f] : Mono (uliftForPresentationMap.{u, v, r, m, t} f) := by
  apply (SheafOfModules.forget R).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  have : Mono f.val := (SheafOfModules.forget R).map_mono f
  intro U x y h
  exact ULift.ext ((PresheafOfModules.injective_of_mono f.val U) (congrArg ULift.down h))

end UniverseLift

end SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-- The direct-sum clause of Stacks 03M1 for the small étale ringed site of an algebraic space,
in the module universe enlarged to contain the site: a direct sum of quasi-coherent modules is
quasi-coherent.  The direct sum is given by its universal property, so no cocompleteness
instance is assumed. -/
def IsClosedUnderDirectSumsQuasicoherent : Prop :=
  ∀ (I : Type (max (u + 1) m)) (F : I → Modules.{u, max (u + 1) m} B S hS X hX)
    (c : Limits.Cofan F), Limits.IsColimit c → (∀ i, (F i).IsQuasicoherentOnSite) →
      c.pt.IsQuasicoherentOnSite

section Closure

variable [ObjectProperty.IsClosedUnderKernels
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)))]
  [ObjectProperty.IsClosedUnderCokernels
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, max (u + 1) m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)))]

/-- The image of a map into a quasi-coherent module is quasi-coherent: it agrees with the image
of the composite with a monomorphism into a quasi-coherent module, and that image is the kernel
of the cokernel projection of the composite. -/
private theorem isQuasicoherentOnSite_imageSubobject
    {M G H : Modules.{u, max (u + 1) m} B S hS X hX}
    [M.IsQuasicoherentOnSite] [H.IsQuasicoherentOnSite]
    (g : G ⟶ M) [Mono g] (f : H ⟶ G) :
    (imageSubobject f : Modules.{u, max (u + 1) m} B S hS X hX).IsQuasicoherentOnSite := by
  have hc : (cokernel (f ≫ g)).IsQuasicoherentOnSite :=
    ObjectProperty.prop_cokernel _ (f ≫ g) ‹_› ‹_›
  have hk : (Abelian.image (f ≫ g)).IsQuasicoherentOnSite :=
    ObjectProperty.prop_kernel _ (cokernel.π (f ≫ g)) ‹_› hc
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (Abelian.imageIsoImage (f ≫ g) ≪≫
      (image.isoStrongEpiMono (factorThruImage f) (image.ι f ≫ g) (by simp)).symm ≪≫
      (imageSubobjectIso f).symm) hk

/-- **The construction of Stacks 04CK in the enlarged module universe.**  Inside a
quasi-coherent module, every subobject contains a quasi-coherent subobject through which every
map from a quasi-coherent module factors uniquely: take the image of the direct sum of all the
quasi-coherent subobjects.

The module universe is enlarged to contain the small étale site, which is what makes the
subobject lattice small and the direct sum exist. -/
private theorem exists_isQuasicoherentOnSite_subobject_bijective_large
    (hsum : IsClosedUnderDirectSumsQuasicoherent.{u, m} B S hS X hX)
    (M G : Modules.{u, max (u + 1) m} B S hS X hX) [M.IsQuasicoherentOnSite]
    (g : G ⟶ M) [Mono g] :
    ∃ P : Subobject G,
      (P : Modules.{u, max (u + 1) m} B S hS X hX).IsQuasicoherentOnSite ∧
        ∀ (H : Modules.{u, max (u + 1) m} B S hS X hX) [H.IsQuasicoherentOnSite],
          Function.Bijective
            (fun f : H ⟶ (P : Modules.{u, max (u + 1) m} B S hS X hX) ↦ f ≫ P.arrow) := by
  classical
  have : IsGrothendieckAbelian.{max (u + 1) m}
      (Modules.{u, max (u + 1) m} B S hS X hX) :=
    Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck.{u + 1, u, u, m} _
  set E := equivShrink.{max (u + 1) m} (Subobject G)
  set I := {i : Shrink.{max (u + 1) m} (Subobject G) //
    (E.symm i : Modules.{u, max (u + 1) m} B S hS X hX).IsQuasicoherentOnSite}
  set F : I → Modules.{u, max (u + 1) m} B S hS X hX := fun i ↦ E.symm i.1
  have hFqc (i : I) : (F i).IsQuasicoherentOnSite := i.2
  have : (∐ F).IsQuasicoherentOnSite :=
    hsum I F (Limits.Cofan.mk (∐ F) (Limits.Sigma.ι F)) (Limits.coproductIsCoproduct F) hFqc
  set ψ : ∐ F ⟶ G := Sigma.desc fun i ↦ (E.symm i.1).arrow with hψ
  refine ⟨imageSubobject ψ, isQuasicoherentOnSite_imageSubobject B S hS X hX g ψ,
    fun H hH ↦ ⟨fun _ _ h ↦ (cancel_mono _).mp h, fun f ↦ ?_⟩⟩
  set i : I := ⟨E (imageSubobject f),
    by simpa using isQuasicoherentOnSite_imageSubobject B S hS X hX g f⟩ with hi
  refine ⟨factorThruImageSubobject f ≫ (Subobject.isoOfEq _ (E.symm i.1) (by simp [hi])).hom ≫
    Sigma.ι F i ≫ factorThruImageSubobject ψ, ?_⟩
  change (factorThruImageSubobject f ≫ _ ≫ Sigma.ι F i ≫ factorThruImageSubobject ψ) ≫
    (imageSubobject ψ).arrow = f
  rw [Category.assoc, Category.assoc, Category.assoc, imageSubobject_arrow_comp, hψ,
    Sigma.ι_comp_desc, Subobject.isoOfEq_hom, Subobject.ofLE_arrow, imageSubobject_arrow_comp]

/-- **The construction of Stacks 04CK.**  Inside a quasi-coherent `𝒪_X`-module, every submodule
contains a quasi-coherent submodule through which every map from a quasi-coherent module
factors uniquely. -/
private theorem exists_isQuasicoherentOnSite_subobject_bijective
    (hsum : IsClosedUnderDirectSumsQuasicoherent.{u, m} B S hS X hX)
    (M : Modules.{u, m} B S hS X hX) [M.IsQuasicoherentOnSite] (G : Subobject M) :
    ∃ P : Subobject (G : Modules.{u, m} B S hS X hX),
      (P : Modules.{u, m} B S hS X hX).IsQuasicoherentOnSite ∧
        ∀ (H : Modules.{u, m} B S hS X hX) [H.IsQuasicoherentOnSite],
          Function.Bijective
            (fun f : H ⟶ (P : Modules.{u, m} B S hS X hX) ↦ f ≫ P.arrow) := by
  classical
  have hM := SheafOfModules.isQuasicoherentOnSite_uliftForPresentation.{u + 1, u, u, m}
    (M := M) ‹_›
  have : Mono (SheafOfModules.uliftForPresentationMap.{u + 1, u, u, m, u + 1} G.arrow) :=
    SheafOfModules.mono_uliftForPresentationMap G.arrow
  obtain ⟨P, hP, hfac⟩ := exists_isQuasicoherentOnSite_subobject_bijective_large B S hS X hX hsum
    (SheafOfModules.uliftForPresentation.{u + 1, u, u, m, u + 1} M)
    (SheafOfModules.uliftForPresentation.{u + 1, u, u, m, u + 1} (G : Modules.{u, m} B S hS X hX))
    (SheafOfModules.uliftForPresentationMap.{u + 1, u, u, m, u + 1} G.arrow)
  set N := SheafOfModules.monoRangeSubmodule P.arrow
  set D := SheafOfModules.submoduleOfUlift.{u + 1, u, u, m, u + 1} N
  have hD : D.toSheafOfModules.IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_uliftForPresentation
      (SheafOfModules.IsQuasicoherentOnSite.of_iso
        (SheafOfModules.uliftSubmoduleOfUliftIso N).symm
        (SheafOfModules.IsQuasicoherentOnSite.of_iso
          (SheafOfModules.isoMonoRangeSubmodule P.arrow) hP))
  refine ⟨Subobject.mk D.ι,
    SheafOfModules.IsQuasicoherentOnSite.of_iso (Subobject.underlyingIso D.ι).symm hD,
    fun H hH ↦ ⟨fun _ _ h ↦ (cancel_mono _).mp h, fun f ↦ ?_⟩⟩
  have hH' := SheafOfModules.isQuasicoherentOnSite_uliftForPresentation.{u + 1, u, u, m}
    (M := H) hH
  obtain ⟨c, hc⟩ := (hfac (SheafOfModules.uliftForPresentation.{u + 1, u, u, m, u + 1} H)).2
    (SheafOfModules.uliftForPresentationMap.{u + 1, u, u, m, u + 1} f)
  have hι : (SheafOfModules.uliftSubmoduleOfUliftIso N).hom ≫ N.ι =
      SheafOfModules.uliftForPresentationMap.{u + 1, u, u, m, u + 1} D.ι := by
    ext U x
    rfl
  have he : (SheafOfModules.isoMonoRangeSubmodule P.arrow).hom ≫ N.ι = P.arrow := by
    ext U x
    rfl
  set l := c ≫ (SheafOfModules.isoMonoRangeSubmodule P.arrow).hom ≫
    (SheafOfModules.uliftSubmoduleOfUliftIso N).inv with hlDef
  have hl : l ≫ SheafOfModules.uliftForPresentationMap.{u + 1, u, u, m, u + 1} D.ι =
      SheafOfModules.uliftForPresentationMap.{u + 1, u, u, m, u + 1} f := by
    rw [hlDef, ← hι]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, he] using hc
  refine ⟨SheafOfModules.mapOfUliftMap l ≫ (Subobject.underlyingIso D.ι).inv, ?_⟩
  change (SheafOfModules.mapOfUliftMap l ≫ (Subobject.underlyingIso D.ι).inv) ≫
    (Subobject.mk D.ι).arrow = f
  rw [Category.assoc, Subobject.underlyingIso_arrow]
  ext U x
  exact congrArg (fun z ↦ (z.val.app U (ULift.up x)).down) hl

/-- **The statement of Stacks 04CK, reduced to the closure clauses of Stacks 03M1.**  Let `M` be
a quasi-coherent `𝒪_X`-module on an algebraic space `X` and let `G ⊆ M` be an `𝒪_X`-submodule.
There is a unique quasi-coherent submodule `G' ⊆ G` for which composition with the inclusion
`G' ⊆ G` is a bijection `Hom(H, G') ⟶ Hom(H, G)` for every quasi-coherent `𝒪_X`-module `H`.

The three hypotheses are the clauses of Stacks 03M1 which this tree does not yet have; see the
implementation notes. -/
theorem existsUnique_quasicoherentSubobject_of_closure
    (hsum : IsClosedUnderDirectSumsQuasicoherent.{u, m} B S hS X hX)
    (M : Modules.{u, m} B S hS X hX) [M.IsQuasicoherentOnSite] (G : Subobject M) :
    ∃! G' : { G' : Subobject (G : Modules.{u, m} B S hS X hX) //
        (G' : Modules.{u, m} B S hS X hX).IsQuasicoherentOnSite },
      ∀ (H : Modules.{u, m} B S hS X hX) [H.IsQuasicoherentOnSite],
        Function.Bijective
          (fun f : H ⟶ (G'.1 : Modules.{u, m} B S hS X hX) ↦ f ≫ G'.1.arrow) := by
  obtain ⟨P, hP, hfac⟩ :=
    exists_isQuasicoherentOnSite_subobject_bijective B S hS X hX hsum M G
  refine ⟨⟨P, hP⟩, hfac, fun Q hQ ↦ Subtype.ext (le_antisymm ?_ ?_)⟩
  · have := Q.2
    exact Subobject.le_of_comm _ ((hfac Q.1).2 Q.1.arrow).choose_spec
  · have := hP
    exact Subobject.le_of_comm _ ((hQ P).2 P.arrow).choose_spec

/-- **The maximality clause of Stacks 04CK, reduced to the closure clauses of Stacks 03M1.**
The quasi-coherent submodule of
`AlgebraicGeometry.Space.existsUnique_quasicoherentSubobject_of_closure` is the largest
quasi-coherent submodule contained in `G`: every quasi-coherent submodule of `G` is contained
in it. -/
theorem exists_greatest_quasicoherentSubobject_of_closure
    (hsum : IsClosedUnderDirectSumsQuasicoherent.{u, m} B S hS X hX)
    (M : Modules.{u, m} B S hS X hX) [M.IsQuasicoherentOnSite] (G : Subobject M) :
    ∃ G' : Subobject (G : Modules.{u, m} B S hS X hX),
      (G' : Modules.{u, m} B S hS X hX).IsQuasicoherentOnSite ∧
        ∀ K : Subobject (G : Modules.{u, m} B S hS X hX),
          (K : Modules.{u, m} B S hS X hX).IsQuasicoherentOnSite → K ≤ G' := by
  obtain ⟨P, hfac, -⟩ :=
    existsUnique_quasicoherentSubobject_of_closure B S hS X hX hsum M G
  refine ⟨P.1, P.2, fun K hK ↦ ?_⟩
  have := hK
  exact Subobject.le_of_comm _ ((hfac K).2 K.arrow).choose_spec

end Closure

end AlgebraicGeometry.Space

end
