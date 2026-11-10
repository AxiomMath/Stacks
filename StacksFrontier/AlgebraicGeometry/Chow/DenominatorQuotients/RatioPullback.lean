module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder.Stalk
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.SectionPullback
public import StacksFrontier.AlgebraicGeometry.Divisors.MeromorphicStalk
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction

/-!
# The pullback of a local ratio representing a meromorphic section

Let `f : X ⟶ Y` be a morphism of locally ringed spaces for which pullbacks of meromorphic
functions are defined, let `F` be a sheaf of `𝒪_Y`-modules and let `s` be a meromorphic section
of `F`. If over an open set `V` of `Y` the section is represented by a ratio, that is

  `b · s|_V = a · g`   in   `Γ(𝒦_Y(F), V)`

for sections `a`, `b` of `𝒪_Y` and a section `g` of `F`, then the same holds over `f⁻¹V` for the
pullback `f^* s` of [Stacks, Tag 02OY] part (1), with the pullbacks of `a`, `b` and `g`.

## Main results

* `AlgebraicGeometry.pullbackMeromorphicSection_eval'` — the value of the pullback of a
  meromorphic section over the preimage of an open set is the component there of the pullback
  morphism on sheaves of meromorphic sections.
* `AlgebraicGeometry.smul_pullbackMeromorphicSection_val_eq` — the statement above.
* `AlgebraicGeometry.bijective_smul_germ_pullbackUnit'` and
  `AlgebraicGeometry.isStalkBasis_pullbackUnit` — the pullback of a section whose germ is a stalk
  basis has germ a stalk basis: the stalk of a pullback is a base change (Tag 0098), and a base
  change of a free rank-one module is free of rank one.

## Implementation notes

Neither statement is in the library: part (1) of the tag, in
`StacksFrontier/AlgebraicGeometry/Divisors/Meromorphic/SectionPullback.lean`, builds the pullback
morphism but does not read a value off it over the preimage of an open set, and part (2), in
`StacksFrontier/AlgebraicGeometry/Divisors/Meromorphic/SectionPullbackRegular.lean`, works at the
generic point and so never needs a ratio. They are proved here from the public API of part (1):
the characterization `AlgebraicGeometry.unit_comp_meromorphicSectionSheafPullback` of the
pullback morphism on sheaves of meromorphic sections, and the commuting square
`AlgebraicGeometry.toTotalQuotient_comp_totalQuotientRingCatSheafPullback` of the two
localization maps and the two pullback maps.

The same applies to the pullback of a stalk basis, which is proved here from the public
`AlgebraicGeometry.RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`
(Tag 0098). That statement is given for Mathlib's module structure on the stalk of a presheaf of
modules, while the library also carries
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`, a second structure on the same stalk
which is equal but not definitionally so and which wins instance search; Mathlib's is therefore
given local priority here as `AlgebraicGeometry.mathlibStalkModule'`.

## References

* [Stacks Project, Tag 02OY](https://stacks.math.columbia.edu/tag/02OY)
* [Stacks Project, Tag 02OT](https://stacks.math.columbia.edu/tag/02OT)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A sheaf of `𝒪_Z`-modules read as a presheaf of modules over the structure sheaf in the
syntactic form at which Mathlib registers the action of `𝒪_Z(V)` on the sections over `V`;
instance search does not cross between this form and
`AlgebraicGeometry.LocallyRingedSpace.ringCatSheaf`. -/
abbrev valOn {Z : LocallyRingedSpace.{u}}
    (N : SheafOfModules.{u} (LocallyRingedSpace.ringCatSheaf Z)) :
    PresheafOfModules.{u} (Z.presheaf ⋙ forget₂ CommRingCat RingCat) := N.val

/-- The image in `𝒦_Z` of a section of `𝒪_Z`, at the declared type at which the action on the
sections of a sheaf of meromorphic sections is registered. -/
abbrev toKScalar (Z : LocallyRingedSpace.{u}) (V : Opens Z) (b : Z.presheaf.obj (op V)) :
    (LocallyRingedSpace.totalQuotientRingCatSheaf Z).obj.obj (op V) :=
  ((LocallyRingedSpace.toTotalQuotientRingCatSheaf Z).hom.app (op V)).hom b

/-- The image of a section of a sheaf of `𝒪_Z`-modules in its sheaf of meromorphic sections, at
the declared type at which the action of `𝒦_Z(V)` is registered. -/
abbrev toKModule {Z : LocallyRingedSpace.{u}}
    (N : SheafOfModules.{u} (LocallyRingedSpace.ringCatSheaf Z)) (V : Opens Z)
    (t : N.val.obj (op V)) : (meromorphicSectionSheaf Z.sheaf N).val.obj (op V) :=
  ((Stacks.Divisors.toMeromorphicSectionSheaf Z.sheaf N).app (op V)).hom t

variable {X Y : LocallyRingedSpace.{u}} {f : X ⟶ Y} (hf : PullbacksMeromorphicSections f)
  (F : SheafOfModules.{u} (LocallyRingedSpace.ringCatSheaf Y))

/-- **The value of the pullback of a meromorphic section over the preimage of an open set** is the
component there of the pullback morphism on sheaves of meromorphic sections. The pullback is read
off at the top open set, whose preimage is the whole source space, and the restriction maps of a
direct image are those of the source over preimages. -/
theorem pullbackMeromorphicSection_eval' (s : MeromorphicSection Y.sheaf F) (V : Opens Y) :
    (pullbackMeromorphicSection f hf F s).eval (op ((Opens.map f.base).obj V))
      = (meromorphicSectionSheafPullback f hf F).val.app (op V) (s.eval (op V)) := by
  have hnat := PresheafOfModules.naturality_apply
    (meromorphicSectionSheafPullback f hf F).val (homOfLE (le_top : V ≤ ⊤)).op (s.eval (op ⊤))
  rw [PresheafOfModules.sections_property s (homOfLE (le_top : V ≤ ⊤)).op] at hnat
  rw [hnat]
  exact congrArg
    (fun i : op ((Opens.map f.base).obj ⊤) ⟶ op ((Opens.map f.base).obj V) =>
      ((meromorphicSectionSheaf X.sheaf
          ((RingedSpaceModuleAdjunction.modulePullback f.toShHom).obj F)).val.map i).hom
        ((meromorphicSectionSheafPullback f hf F).val.app (op ⊤) (s.eval (op ⊤))))
    (Subsingleton.elim _ _)

/-- **The pullback of a local ratio representing a meromorphic section.** If `b · s = a · g` over
`V`, then the same identity holds over `f⁻¹V` between the pullback of `s` and the pullbacks of
`a`, `b` and `g`. -/
theorem smul_pullbackMeromorphicSection_val_eq (s : MeromorphicSection Y.sheaf F) {V : Opens Y}
    (g : (valOn F).obj (op V)) (b a : Y.presheaf.obj (op V))
    (heq : toKScalar Y V b •
          s.eval (op V) =
        toKModule F V (a • g)) :
    toKScalar X ((Opens.map f.base).obj V) (Stacks.RingedSpace.sharp f.toShHom (op V) b) •
          (pullbackMeromorphicSection f hf F s).eval (op ((Opens.map f.base).obj V)) =
      toKScalar X ((Opens.map f.base).obj V) (Stacks.RingedSpace.sharp f.toShHom (op V) a) •
        toKModule ((RingedSpaceModuleAdjunction.modulePullback f.toShHom).obj F)
          ((Opens.map f.base).obj V)
          (Stacks.RingedSpace.pullbackUnit f.toShHom F (op V) g) := by
  have hΦ := congrArg (fun z : (meromorphicSectionSheaf Y.sheaf F).val.obj (op V) =>
    (meromorphicSectionSheafPullback f hf F).val.app (op V) z) heq
  have hsq : ((totalQuotientRingCatSheafPullback f hf).hom.app (op V)).hom (toKScalar Y V b) =
      toKScalar X ((Opens.map f.base).obj V) (Stacks.RingedSpace.sharp f.toShHom (op V) b) :=
    (congrArg (fun k : LocallyRingedSpace.ringCatSheaf Y ⟶
      (ringCatSheafPushforward f).obj (LocallyRingedSpace.totalQuotientRingCatSheaf X) =>
        (k.hom.app (op V)).hom b)
      (toTotalQuotient_comp_totalQuotientRingCatSheafPullback f hf)).symm
  have hL1 : toKScalar X ((Opens.map f.base).obj V) (Stacks.RingedSpace.sharp f.toShHom (op V) b) •
          (pullbackMeromorphicSection f hf F s).eval (op ((Opens.map f.base).obj V)) =
      (meromorphicSectionSheafPullback f hf F).val.app (op V)
        (toKScalar Y V b • s.eval (op V)) := by
    rw [pullbackMeromorphicSection_eval' hf F s V,
      ((meromorphicSectionSheafPullback f hf F).val.app (op V)).hom.map_smul
        (toKScalar Y V b) (s.eval (op V)), ← hsq]
    exact rfl
  have hunit : (meromorphicSectionSheafPullback f hf F).val.app (op V)
        (toKModule F V (a • g)) =
      toKModule ((RingedSpaceModuleAdjunction.modulePullback f.toShHom).obj F)
        ((Opens.map f.base).obj V)
        (Stacks.RingedSpace.pullbackUnit f.toShHom F (op V) (a • g)) :=
    congrArg (fun φ : F ⟶ (SheafOfModules.restrictScalars
          (LocallyRingedSpace.toTotalQuotientRingCatSheaf Y)).obj
        ((SheafOfModules.pushforward (totalQuotientRingCatSheafPullback f hf)).obj
          (meromorphicSectionSheaf X.sheaf
            ((RingedSpaceModuleAdjunction.modulePullback f.toShHom).obj F))) =>
      φ.val.app (op V) (a • g)) (unit_comp_meromorphicSectionSheafPullback f hf F)
  have hR1 : (meromorphicSectionSheafPullback f hf F).val.app (op V)
        (toKModule F V (a • g)) =
      toKScalar X ((Opens.map f.base).obj V) (Stacks.RingedSpace.sharp f.toShHom (op V) a) •
        toKModule ((RingedSpaceModuleAdjunction.modulePullback f.toShHom).obj F)
          ((Opens.map f.base).obj V)
          (Stacks.RingedSpace.pullbackUnit f.toShHom F (op V) g) := by
    refine Eq.trans hunit (Eq.trans (congrArg
      (toKModule ((RingedSpaceModuleAdjunction.modulePullback f.toShHom).obj F)
        ((Opens.map f.base).obj V))
      (Stacks.RingedSpace.pullbackUnit_smul f.toShHom F (op V) a g)) ?_)
    exact ((Stacks.Divisors.toMeromorphicSectionSheaf X.sheaf
      ((RingedSpaceModuleAdjunction.modulePullback f.toShHom).obj F)).app
        (op ((Opens.map f.base).obj V))).hom.map_smul
          (Stacks.RingedSpace.sharp f.toShHom (op V) a)
          (Stacks.RingedSpace.pullbackUnit f.toShHom F (op V) g)
  rw [hL1, hΦ, hR1]

/-! ### The pullback of a stalk basis -/

/-- **Base change of a free rank-one module is free of rank one.** If `M` is generated freely
over `A` by `m`, and `j : M ⟶ N` exhibits `N` as the base change of `M` along `A ⟶ B`, then `N` is
generated freely over `B` by `j m`. -/
theorem bijective_smul_of_isBaseChange {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module B N] [IsScalarTower A B N] {j : M →ₗ[A] N} (h : IsBaseChange B j) {m : M}
    (hm : Function.Bijective fun c : A => c • m) :
    Function.Bijective fun z : B => z • j m := by
  let u : A ≃ₗ[A] M := LinearEquiv.ofBijective (LinearMap.toSpanSingleton A M m) hm
  have hu : u 1 = m := one_smul A m
  have h1 : (fun z : B => z ⊗ₜ[A] m) =
      (LinearEquiv.lTensor B u) ∘ (TensorProduct.rid A B).symm := by
    funext z
    change z ⊗ₜ[A] m = (LinearEquiv.lTensor B u) ((TensorProduct.rid A B).symm z)
    rw [TensorProduct.rid_symm_apply, LinearEquiv.lTensor_tmul, hu]
  have h2 : (fun z : B => z • j m) = h.equiv ∘ (fun z : B => z ⊗ₜ[A] m) :=
    funext fun z => (h.equiv_tmul z m).symm
  rw [h2, h1]
  exact h.equiv.bijective.comp
    ((LinearEquiv.lTensor B u).bijective.comp (TensorProduct.rid A B).symm.bijective)

/-- Mathlib's module structure on the stalk of a presheaf of modules over a presheaf of
commutative rings, named so that it can be given priority; see the implementation notes. -/
abbrev mathlibStalkModule' {T : TopCat.{u}} (R : T.Presheaf CommRingCat.{u})
    (N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) (t : T) :
    Module ↑(R.stalk t) ↑(TopCat.Presheaf.stalk N.presheaf t) :=
  inferInstance

attribute [local instance 10000] mathlibStalkModule'

/-- **The pullback of a free generator generates the stalk of the pullback freely.** If a section
`g` of `G` over `V` generates the stalk of `G` at `f x` freely, then the section of `f^* G` over
`f⁻¹V` obtained from `g` by the unit of `f^* ⊣ f_*` generates the stalk of `f^* G` at `x`
freely. -/
theorem bijective_smul_germ_pullbackUnit' (f : X ⟶ Y)
    (G : SheafOfModules.{u} (LocallyRingedSpace.ringCatSheaf Y)) (x : X) (V : Opens Y)
    (hx : f.toShHom.hom.base x ∈ V) (g : (valOn G).obj (op V))
    (hg : Function.Bijective fun c : Y.presheaf.stalk (f.toShHom.hom.base x) =>
      c • Stacks.ModuleStalk.germ (valOn G) V (f.toShHom.hom.base x) hx g) :
    Function.Bijective fun c : X.presheaf.stalk x =>
      c • Stacks.ModuleStalk.germ
        (valOn ((RingedSpaceModuleAdjunction.modulePullback f.toShHom).obj G))
        ((RingedSpaceModuleAdjunction.opensMap f.toShHom).obj V) x hx
        (Stacks.RingedSpace.pullbackUnit f.toShHom G (op V) g) := by
  let : Algebra ↑(Y.presheaf.stalk (f.toShHom.hom.base x)) ↑(X.presheaf.stalk x) :=
    (f.toShHom.hom.stalkMap x).hom.toAlgebra
  obtain ⟨e, he⟩ :=
    RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv f.toShHom G x
  have hbc : IsBaseChange ↑(X.presheaf.stalk x)
      (TensorProduct.mk ↑(Y.presheaf.stalk (f.toShHom.hom.base x)) ↑(X.presheaf.stalk x)
        ↑(TopCat.Presheaf.stalk (Stacks.ModuleStalk.presheafOn (valOn G))
          (f.toShHom.hom.base x)) 1) :=
    TensorProduct.isBaseChange _ _ _
  have hkey : (fun c : ↑(X.presheaf.stalk x) =>
        c • Stacks.ModuleStalk.germ
          (valOn ((RingedSpaceModuleAdjunction.modulePullback f.toShHom).obj G))
          ((RingedSpaceModuleAdjunction.opensMap f.toShHom).obj V) x hx
          (Stacks.RingedSpace.pullbackUnit f.toShHom G (op V) g)) =
      e.symm ∘ (fun z : ↑(X.presheaf.stalk x) =>
        z • ((1 : ↑(X.presheaf.stalk x)) ⊗ₜ[↑(Y.presheaf.stalk (f.toShHom.hom.base x))]
          Stacks.ModuleStalk.germ (valOn G) V (f.toShHom.hom.base x) hx g)) := by
    funext c
    change c • Stacks.ModuleStalk.germ
          (valOn ((RingedSpaceModuleAdjunction.modulePullback f.toShHom).obj G))
          ((RingedSpaceModuleAdjunction.opensMap f.toShHom).obj V) x hx
          (Stacks.RingedSpace.pullbackUnit f.toShHom G (op V) g)
        = e.symm (c • ((1 : ↑(X.presheaf.stalk x))
          ⊗ₜ[↑(Y.presheaf.stalk (f.toShHom.hom.base x))]
          Stacks.ModuleStalk.germ (valOn G) V (f.toShHom.hom.base x) hx g))
    rw [LinearEquiv.map_smul e.symm, ← he V hx g, e.symm_apply_apply]
    rfl
  rw [hkey]
  exact e.symm.bijective.comp (bijective_smul_of_isBaseChange hbc hg)

end AlgebraicGeometry

end
