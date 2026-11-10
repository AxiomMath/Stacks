module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ChangeOfRingsAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekFreeModuleBaseChange
public import StacksFrontier.Cotangent.Triangle.Distinguished
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat base change for simplicial modules: the site `Δ` of Stacks 08RX

[Stacks, Tag 08RX] is the statement that, on a site with a cosimplicial point resolution, a map
`O ⟶ B̲` of sheaves of rings which derived lower shriek inverts continues to be inverted after
tensoring with a flat module. Remark [Stacks, Tag 08QD] specialises the whole setting of homology
on a category to `C = Δ`, where the chaotic topology is invisible — every presheaf on `Δ` is a
sheaf for it — and where the tautological cosimplicial object `U_• = 𝟭` is a point resolution
because the standard simplices are contractible
(`Stacks.ChaoticSite.isPointResolution_id_simplexCategory`). The instance of 08RX at that site is
the "key fact" of Remark [Stacks, Tag 08SD] and the last input of [Stacks, Tag 08QX].

Written out at `C = Δ`, the assertion concerns a simplicial commutative ring `O`, a commutative
ring `B` and an augmentation `φ : O ⟶ B̲` to the constant simplicial ring, and reads:

> if the base-change unit `s(O_•) ⟶ s(B̲)` is a quasi-isomorphism of Moore complexes, then
> `s(Q_•) ⟶ s(Q_• ⊗_{O_•} B̲)` is a quasi-isomorphism for every simplicial `O`-module `Q` which
> is flat in every simplicial degree.

Here `s(-)` is the Moore complex of the underlying simplicial abelian group, read as a cochain
complex over `ℤ` with simplicial degree `n` in cohomological degree `-n`
(`AlgebraicTopology.alternatingFaceMapCochainComplex`), and the hypothesis is stated at the
structure sheaf because `O ⊗_O B = B̲`.

This file sets up that statement — `Stacks.SimplicialModules.SMod`,
`Stacks.SimplicialModules.mooreCochain` and `Stacks.SimplicialModules.mooreCochainBaseChange` —
and proves its **column step**: the base-change unit is a quasi-isomorphism at the canonical
cover of a simplicial module by free simplicial modules on standard simplices
(`Stacks.SimplicialModules.quasiIso_mooreCochainBaseChange_app_stdCover`). What remains is the
assembly of the two filtrations of a double complex; see the implementation notes.

## Main definitions

* `PresheafOfModules.freeUliftYonedaEquiv`: maps out of the free presheaf of modules on a
  *universe-lifted* representable are the sections over the representing object.
* `PresheafOfModules.stdCover` and `PresheafOfModules.fromStdCover`: the presentation of a
  presheaf of modules by the coproduct, indexed by its sections, of the free presheaves of
  modules on the universe-lifted representables.
* `AddCommGrpCat.finsuppCopowerIso`: the free abelian group on a set with values in `M` is the
  copower of `M` by that set.
* `PresheafOfModules.copowerFreeIso`: the underlying presheaf of abelian groups of the free
  presheaf of modules `R⟨F⟩` on a presheaf of sets `F` is the copower of the structure presheaf
  by `F`.
* `Stacks.PresheafOfModules.ChangeOfRings.unitMap`: a morphism of presheaves of commutative rings
  read on the underlying presheaves of abelian groups of the structure presheaves of modules.
* `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsFreeCopowerIso`: the base change of
  `R⟨F⟩` has underlying presheaf of abelian groups the copower of the *target* structure presheaf
  by `F`.
* `CochainComplex.discreteFamily` and `CochainComplex.sigmaIsoDiscreteFamily`: a family of
  cochain complexes read as a cochain complex of diagrams on a discrete category, and the
  identification of its degreewise colimit with the coproduct of the family.
* `Stacks.SimplicialModules.SMod`, `Stacks.SimplicialModules.mooreCochain` and
  `Stacks.SimplicialModules.mooreCochainBaseChange`: simplicial modules over a simplicial
  commutative ring, their Moore cochain complexes, and the base-change unit read on those.
* `Stacks.SimplicialModules.stdSimplexZeroIsoConst`: the standard zero-simplex is the constant
  simplicial set on a singleton.

## Main results

* `PresheafOfModules.uliftFreeYonedaProjective` and
  `PresheafOfModules.enoughProjectives_of_smallType`: **presheaves of modules on a category whose
  objects and morphisms form types in `Type 0` have enough projectives, for a presheaf of rings
  in an arbitrary universe.**
* `AlgebraicTopology.quasiIso_alternatingFaceMapCochainComplex_map_iff`: a map of simplicial
  objects is a quasi-isomorphism on reindexed Moore complexes exactly when the homology of the
  Moore complex inverts it in every degree.
* `AlgebraicTopology.quasiIso_alternatingFaceMapCochainComplex_map_copowerMap`: **a map of
  simplicial objects which is a quasi-isomorphism on Moore complexes stays one after
  multiplication by a contractible simplicial set.**
* `AlgebraicTopology.preservesColimitsOfShape_alternatingFaceMapCochainComplex`: the reindexed
  Moore complex preserves colimits.
* `Stacks.PresheafOfModules.ChangeOfRings.copowerFreeIso_unitMap_copowerMap`: **the base-change
  unit at a free presheaf of modules is, under the two copower identifications, the copower by
  `F` of the morphism of structure presheaves.**
* `CochainComplex.quasiIso_sigmaMap`: **Grothendieck's axiom AB4 for quasi-isomorphisms** — a
  coproduct of quasi-isomorphisms of cochain complexes is a quasi-isomorphism, as soon as
  coproducts of that shape are exact.
* `CochainComplex.quasiIso_app_sigma`: a natural transformation between coproduct-preserving
  functors to cochain complexes is a quasi-isomorphism at a coproduct as soon as it is one at
  every summand.
* `Stacks.SimplicialModules.quasiIso_mooreCochainBaseChange_app_free` and
  `Stacks.SimplicialModules.quasiIso_mooreCochainBaseChange_app_freeStdSimplex`: **the
  base-change unit is a quasi-isomorphism at the free simplicial module on a contractible
  simplicial set**, in particular on a standard simplex.
* `Stacks.SimplicialModules.quasiIso_mooreCochainBaseChange_app_stdCover`: **the column step of
  the Δ-instance of [Stacks, Tag 08RX]** — the base-change unit is a quasi-isomorphism at
  `PresheafOfModules.stdCover M` for every simplicial module `M`.

## Implementation notes

**The universe obstruction, and why the cover is built from the lifted Yoneda embedding.**
Mathlib's presentation of a presheaf of modules by free presheaves on representables
(`PresheafOfModules.fromFreeYonedaCoproduct`, and `PresheafOfModules.enoughProjectives` in
`StacksFrontier/CategoryTheory/Sites/Cohomology/ChaoticSite/DerivedLowerShriek.lean` which rests on
it) is stated for `C : Type u` with `[SmallCategory.{u} C]` and `R : Cᵒᵖ ⥤ RingCat.{u}`: the
Yoneda presheaf `yoneda.obj X : Cᵒᵖ ⥤ Type v₁` can only be fed to
`PresheafOfModules.free R : (Cᵒᵖ ⥤ Type u) ⥤ PresheafOfModules.{u} R` when the hom universe of
`C` equals the ring universe. At `C = Δ`, which lives in `Type 0` with hom types in `Type 0`,
that pins the rings to `RingCat.{0}`, and the rings of 08SD are not in `Type 0`.

Replacing `yoneda` by the universe-lifted Yoneda embedding `uliftYoneda.{u}` — which is
`SSet.stdSimplex.{u}` at `C = Δ`, by definition — removes the constraint: `uliftYoneda.{u}.obj X`
is a presheaf of types in `Type (max u v₁)`, so it can be fed to `free R` for a presheaf of rings
in `RingCat.{u}` as soon as `v₁ ≤ u`. The proofs are Mathlib's, with `yonedaEquiv` replaced by
`uliftYonedaEquiv`. The statements here are given for `C : Type` with `[SmallCategory C]`, which
is the hypothesis `u₁ = v₁ = 0`; that covers `Δ` and keeps the universe arithmetic implicit.

**What the copower identification is for.** The column step of the intended proof — that the
base-change unit is a quasi-isomorphism at the terms of a resolution — is reduced by
`PresheafOfModules.copowerFreeIso` and
`AlgebraicTopology.quasiIso_alternatingFaceMapCochainComplex_map_copowerMap` to the hypothesis at
the structure sheaf: the free presheaf of modules on `Δ[m]` has underlying simplicial abelian
group the product of the contractible simplicial set `Δ[m]` with `O_•`, and multiplying by a
contractible simplicial set does not change which maps the homology of the Moore complex inverts
(`Stacks.ChaoticSite.isIso_mooreHomologyFunctor_map_copowerMap`). The reindexing lemma
`quasiIso_alternatingFaceMapCochainComplex_map_iff` is what transports that statement, which is
about the `ℕ`-indexed Moore complex degree by degree, to the `ℤ`-indexed cochain complex in which
the base-change unit is stated.

**The column step, and why the coproduct needs AB4.** The free simplicial module `O⟨F⟩` on a
simplicial set `F` has underlying simplicial abelian group the product of `F` with `O_•`
(`PresheafOfModules.copowerFreeIso`), its base change has underlying simplicial abelian group the
product of `F` with `B̲` (`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsFreeCopowerIso`),
and the base-change unit is the product of `F` with the augmentation
(`Stacks.PresheafOfModules.ChangeOfRings.copowerFreeIso_unitMap_copowerMap`). Multiplying by a
*contractible* simplicial set does not change which maps the homology of the Moore complex
inverts, so the unit is a quasi-isomorphism at `O⟨Δ[m]⟩`. The cover
`PresheafOfModules.stdCover M` is a coproduct, indexed by the sections of `M`, of such objects,
and only each single `Δ[m]` is contractible, not their disjoint union; what bridges the gap is
Grothendieck's axiom AB4 for `AddCommGrpCat` in the form `CochainComplex.quasiIso_sigmaMap`,
together with the fact that both `mooreCochain O` and `changeOfRings φ ⋙ mooreCochain B̲`
preserve coproducts. AB4 is proved here by reading a family of complexes as a single complex of
diagrams on a discrete category (`CochainComplex.discreteFamily`), whose degreewise colimit is
the coproduct (`CochainComplex.sigmaIsoDiscreteFamily`): exactness of the colimit makes it
preserve homology, and a quasi-isomorphism of complexes of diagrams is one after evaluation at
every index (`HomologicalComplex.quasiIso_iff_evaluation`).

**What is not proved here.** The Δ-instance of 08RX itself is not proved, and nothing carries the
08RX tag. One step remains, and it is not started in this file: the assembly of the two
filtrations of the double complex obtained by applying `mooreCochain O` and
`changeOfRings φ ⋙ mooreCochain B̲` to a resolution of `Q` by objects of the shape
`PresheafOfModules.stdCover`, exactly as in
`Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoDerivedColimitOfResolution`. The intended route
is `CochainComplex.exists_quasiIso_prop` ([Stacks, Tag 05T7]) for the class of objects which are
zero or isomorphic to a `PresheafOfModules.stdCover`, which is discharged by
`PresheafOfModules.fromStdCover`; the terms of such a resolution are sectionwise free, so the row
direction is where the flatness hypothesis on `Q` is consumed, through
`CochainComplex.KFlat.kFlat_of_flat` and
`CochainComplex.DerivedTensor.KFlatDerived.quasiIso_extendScalars_map_of_kFlat` — routed through
`forget₂ (ModuleCat B) AddCommGrpCat`, which preserves homology, because those are stated on
complexes of modules while the rows here live in `AddCommGrpCat`. The columns are
`Stacks.SimplicialModules.quasiIso_mooreCochainBaseChange_app_stdCover`, and the two filtrations
are compared by `StacksDraft.TotalComplexQuasiIso.quasiIso_total_map_of_upperBound` and
`StacksDraft.TotalComplexQuasiIso.quasiIso_total_map_of_upperBound_flip`.

## References

* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
* [Stacks Project, Tag 08QD](https://stacks.math.columbia.edu/tag/08QD)
* [Stacks Project, Tag 08SD](https://stacks.math.columbia.edu/tag/08SD)
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX)
* [Stacks Project, Tag 05T7](https://stacks.math.columbia.edu/tag/05T7)
* [Stacks Project, Tag 079B](https://stacks.math.columbia.edu/tag/079B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

universe w v u

/-! ### Free presheaves of modules on universe-lifted representables -/

namespace PresheafOfModules

variable {C : Type} [SmallCategory C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- **Maps out of the free presheaf of modules on a universe-lifted representable are the
sections over the representing object.** This is `PresheafOfModules.freeYonedaEquiv` with
`CategoryTheory.yoneda` replaced by `CategoryTheory.uliftYoneda`, which is what makes it
available when the hom universe of `C` is smaller than the universe of the presheaf of rings. -/
def freeUliftYonedaEquiv {M : PresheafOfModules.{u} R} {X : C} :
    ((free R).obj (uliftYoneda.{u}.obj X) ⟶ M) ≃ M.obj (op X) :=
  freeHomEquiv.trans uliftYonedaEquiv

/-- `PresheafOfModules.freeUliftYonedaEquiv` evaluates a map at the tautological generator. -/
lemma freeUliftYonedaEquiv_apply {M : PresheafOfModules.{u} R} {X : C}
    (ψ : (free R).obj (uliftYoneda.{u}.obj X) ⟶ M) :
    freeUliftYonedaEquiv ψ = ψ.app (op X) (ModuleCat.freeMk (ULift.up (𝟙 X))) :=
  rfl

/-- `PresheafOfModules.freeUliftYonedaEquiv` is natural in the target. -/
lemma freeUliftYonedaEquiv_comp {M N : PresheafOfModules.{u} R} {X : C}
    (m : (free R).obj (uliftYoneda.{u}.obj X) ⟶ M) (φ : M ⟶ N) :
    freeUliftYonedaEquiv (m ≫ φ) = φ.app _ (freeUliftYonedaEquiv m) :=
  rfl

/-- The map attached to a section carries the tautological generator to that section. -/
lemma freeUliftYonedaEquiv_symm_app (M : PresheafOfModules.{u} R) (X : C)
    (x : M.obj (op X)) :
    (freeUliftYonedaEquiv.symm x).app (op X) (ModuleCat.freeMk (ULift.up (𝟙 X))) = x := by
  rw [← freeUliftYonedaEquiv_apply, Equiv.apply_symm_apply]

/-- **The free presheaf of modules on a universe-lifted representable is projective.** Maps out
of it are the sections over the representing object, and an epimorphism of presheaves of modules
is surjective on sections. -/
@[sga "4 V 2.3.1" "special case"]
instance uliftFreeYonedaProjective (X : C) :
    Projective ((free R).obj (uliftYoneda.{u}.obj X)) where
  factors {_ _} g e he := by
    have := he
    obtain ⟨y, hy⟩ := surjective_of_epi e (op X) (freeUliftYonedaEquiv g)
    exact ⟨freeUliftYonedaEquiv.symm y, freeUliftYonedaEquiv.injective <| by
      rwa [freeUliftYonedaEquiv_comp, Equiv.apply_symm_apply]⟩

/-- The coproduct, indexed by the sections of `M`, of the free presheaves of modules on the
universe-lifted representables. At `C = Δ` the summands are the free presheaves of modules on
the standard simplices, `SSet.stdSimplex` being `CategoryTheory.uliftYoneda` by definition. -/
abbrev stdCover (M : PresheafOfModules.{u} R) : PresheafOfModules.{u} R :=
  ∐ (fun m : M.Elements => (free R).obj (uliftYoneda.{u}.obj m.1.unop))

/-- The canonical map `PresheafOfModules.stdCover M ⟶ M`, given on the summand indexed by a
section by the map that section corresponds to under
`PresheafOfModules.freeUliftYonedaEquiv`. -/
def fromStdCover (M : PresheafOfModules.{u} R) : M.stdCover ⟶ M :=
  Sigma.desc (fun m => freeUliftYonedaEquiv.symm m.2)

/-- **`PresheafOfModules.fromStdCover` is an epimorphism**: the summand indexed by a section
already hits that section. -/
instance epi_fromStdCover (M : PresheafOfModules.{u} R) : Epi M.fromStdCover := by
  refine epi_of_surjective (fun X x => ⟨?_, ?_⟩)
  · exact (Sigma.ι (fun m : M.Elements =>
      (free R).obj (uliftYoneda.{u}.obj m.1.unop)) (M.elementsMk X x)).app X
      (ModuleCat.freeMk (ULift.up (𝟙 X.unop)))
  · have h := ConcreteCategory.congr_hom
      ((evaluation R X ⋙ forget _).congr_map
        (Sigma.ι_comp_desc (fun m : M.Elements => freeUliftYonedaEquiv.symm m.2)
          (M.elementsMk X x))) (ModuleCat.freeMk (ULift.up (𝟙 X.unop)))
    exact h.trans (freeUliftYonedaEquiv_symm_app M X.unop x)

/-- **Presheaves of modules over a presheaf of rings on a category whose objects and morphisms
form types in `Type 0` have enough projectives**, with no constraint relating the universe of
the rings to the site: every presheaf of modules receives an epimorphism from
`PresheafOfModules.stdCover`, a coproduct of free presheaves of modules on the universe-lifted
representables, and those are projective.

`PresheafOfModules.enoughProjectives` is the same statement for a site whose universe equals
that of the rings, which is the generality Mathlib's Yoneda presentation offers. -/
instance enoughProjectives_of_smallType : EnoughProjectives (PresheafOfModules.{u} R) :=
  ⟨fun M => ⟨{ p := M.stdCover, f := M.fromStdCover }⟩⟩

end PresheafOfModules

/-! ### The free abelian group on a set as a copower -/

namespace AddCommGrpCat

/-- **The group of finitely supported functions `S →₀ M` is the copower of `M` by `S`**: it is
the coproduct of `S`-many copies of `M`, the coproduct of modules being computed on underlying
abelian groups. -/
def finsuppCopowerIso (M : Ab.{u}) (S : Type u) :
    AddCommGrpCat.of (S →₀ M) ≅ ∐ (fun _ : S => M) :=
  (isColimitOfPreserves (forget₂ (ModuleCat ℤ) AddCommGrpCat)
    (ModuleCat.finsuppCoconeIsColimit ℤ M S)).coconePointUniqueUpToIso
      (colimit.isColimit (Discrete.functor (fun _ : S => M)))

/-- `AddCommGrpCat.finsuppCopowerIso` carries the summand indexed by `s` to the functions
supported at `s`. -/
lemma ι_finsuppCopowerIso_inv (M : Ab.{u}) (S : Type u) (s : S) :
    Sigma.ι (fun _ : S => M) s ≫ (finsuppCopowerIso M S).inv =
      AddCommGrpCat.ofHom (Finsupp.singleAddHom s) :=
  IsColimit.comp_coconePointUniqueUpToIso_inv
    (isColimitOfPreserves (forget₂ (ModuleCat ℤ) AddCommGrpCat)
      (ModuleCat.finsuppCoconeIsColimit ℤ M S))
    (colimit.isColimit (Discrete.functor (fun _ : S => M))) (Discrete.mk s)

end AddCommGrpCat

/-! ### The free presheaf of modules as a copower of the structure presheaf -/

namespace PresheafOfModules

/-- A multiple of the generator `freeMk s` of a free module is the function supported at `s`. -/
private lemma smul_freeMk_eq_single {R : Type u} [Ring R] {S : Type u} (r : R) (s : S) :
    r • ModuleCat.freeMk (R := R) s = Finsupp.single s r := by
  change r • Finsupp.single s (1 : R) = _
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The summand inclusions of a free presheaf of modules are compatible with restriction maps. -/
private lemma single_comp_map_free {C : Type*} [SmallCategory C] (R : Cᵒᵖ ⥤ RingCat.{u})
    (F : Cᵒᵖ ⥤ Type u) {X Y : Cᵒᵖ} (f : X ⟶ Y) (s : F.obj X) :
    ((toPresheaf R).obj (PresheafOfModules.unit R)).map f ≫
        AddCommGrpCat.ofHom (Finsupp.singleAddHom (F.map f s)) =
      AddCommGrpCat.ofHom (Finsupp.singleAddHom s) ≫
        ((toPresheaf R).obj ((free R).obj F)).map f := by
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun (r : R.obj X) => ?_)
  change Finsupp.single ((F.map f) s) ((R.map f) r) =
    ((free R).obj F).map f (Finsupp.single s r)
  have h3 := PresheafOfModules.map_smul ((free R).obj F) f r
    (ModuleCat.freeMk (R := R.obj X) s)
  rw [show ((free R).obj F).map f (ModuleCat.freeMk (R := R.obj X) s) =
    ModuleCat.freeMk (R := R.obj Y) ((F.map f) s) from ModuleCat.freeDesc_apply _ _] at h3
  exact ((congrArg (((free R).obj F).map f).hom (smul_freeMk_eq_single r s)).symm.trans
    (h3.trans (smul_freeMk_eq_single _ _))).symm

variable {C : Type} [SmallCategory C] (R : Cᵒᵖ ⥤ RingCat.{u}) (F : Cᵒᵖ ⥤ Type u)

/-- The inclusion of the structure presheaf into the free presheaf of modules on `F` as the
summand indexed by a section `s` of `F`, read on underlying presheaves of abelian groups. -/
def freeSingleHom (X : Cᵒᵖ) (s : F.obj X) :
    ((toPresheaf R).obj (PresheafOfModules.unit R)).obj X ⟶
      ((toPresheaf R).obj ((free R).obj F)).obj X :=
  AddCommGrpCat.ofHom (Finsupp.singleAddHom s)

/-- The component of `PresheafOfModules.copowerFreeIso` at an object of the site. -/
def copowerFreeIsoApp (X : Cᵒᵖ) :
    (((toPresheaf R).obj (PresheafOfModules.unit R)).copower F).obj X ≅
      ((toPresheaf R).obj ((free R).obj F)).obj X :=
  (AddCommGrpCat.finsuppCopowerIso
    (((toPresheaf R).obj (PresheafOfModules.unit R)).obj X) (F.obj X)).symm

/-- `PresheafOfModules.copowerFreeIsoApp` carries the summand indexed by a section `s` to its
image under `PresheafOfModules.freeSingleHom`. -/
@[reassoc]
lemma ι_copowerFreeIsoApp_hom (X : Cᵒᵖ) (s : F.obj X) :
    Sigma.ι (fun _ : F.obj X => ((toPresheaf R).obj (PresheafOfModules.unit R)).obj X) s ≫
      (copowerFreeIsoApp R F X).hom = freeSingleHom R F X s :=
  AddCommGrpCat.ι_finsuppCopowerIso_inv _ _ s

/-- The summand inclusions of `PresheafOfModules.freeSingleHom` are compatible with the
restriction maps: restricting and then including at the restricted index agrees with including
and then restricting. -/
lemma freeSingleHom_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) (s : F.obj X) :
    ((toPresheaf R).obj (PresheafOfModules.unit R)).map f ≫ freeSingleHom R F Y (F.map f s) =
      freeSingleHom R F X s ≫ ((toPresheaf R).obj ((free R).obj F)).map f :=
  single_comp_map_free R F f s

/-- **The underlying presheaf of abelian groups of the free presheaf of modules on a presheaf of
sets `F` is the copower of the structure presheaf by `F`.** Over each object the free module on
`F(X)` is the direct sum of `F(X)`-many copies of `R(X)`, and the restriction maps of the free
presheaf of modules permute the summands along those of `F`. -/
def copowerFreeIso :
    ((toPresheaf R).obj (PresheafOfModules.unit R)).copower F ≅
      (toPresheaf R).obj ((free R).obj F) :=
  NatIso.ofComponents (copowerFreeIsoApp R F) fun f => Sigma.hom_ext _ _ fun s => by
    rw [Functor.copower_map, Sigma.ι_comp_map'_assoc, ι_copowerFreeIsoApp_hom,
      ι_copowerFreeIsoApp_hom_assoc]
    exact freeSingleHom_naturality R F f s

end PresheafOfModules

/-! ### Base change of a free presheaf of modules as a copower -/

namespace Stacks.PresheafOfModules.ChangeOfRings

open scoped TensorProduct

variable {C : Type} [SmallCategory C] (O : Cᵒᵖ ⥤ CommRingCat.{u})

/-- The presheaf of abelian groups underlying the structure presheaf of modules of a presheaf of
commutative rings. At `C = Δ` this is the simplicial abelian group underlying a simplicial
commutative ring. -/
abbrev unitPresheaf : Cᵒᵖ ⥤ Ab.{u} :=
  (_root_.PresheafOfModules.toPresheaf (ringPresheaf O)).obj
    (_root_.PresheafOfModules.unit (ringPresheaf O))

variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (θ : O₁ ⟶ O₂)

/-- **A morphism of presheaves of commutative rings read on the underlying presheaves of abelian
groups of the two structure presheaves of modules**: `θ` itself, with the multiplicative
structure forgotten. At `C = Δ` this is the map of simplicial abelian groups `s(O_•) ⟶ s(B̲)`
underlying an augmentation of simplicial rings. -/
def unitMap : unitPresheaf O₁ ⟶ unitPresheaf O₂ where
  app X := AddCommGrpCat.ofHom (θ.app X).hom.toAddMonoidHom
  naturality X Y f := by
    ext (r : O₁.obj X)
    exact congrArg (fun g => CommRingCat.Hom.hom g r) (θ.naturality f)

/-- `Stacks.PresheafOfModules.ChangeOfRings.unitMap` is `θ` on sections. -/
lemma unitMap_app_apply (X : Cᵒᵖ) (r : O₁.obj X) :
    (unitMap θ).app X r = (θ.app X).hom r :=
  rfl

/-- **Base change of presheaves of modules preserves colimits**, being a left adjoint
(`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction`). -/
instance isLeftAdjoint_changeOfRings :
    Functor.IsLeftAdjoint (changeOfRings θ : _root_.PresheafOfModules.{u} (ringPresheaf O₁) ⥤
      _root_.PresheafOfModules.{u} (ringPresheaf O₂)) :=
  ⟨_, ⟨changeOfRingsAdjunction θ⟩⟩

/-- The presheaf of abelian groups underlying the base change along `θ` of the free presheaf of
`O₁`-modules on a presheaf of sets. -/
abbrev changeOfRingsFreePresheaf (F : Cᵒᵖ ⥤ Type u) : Cᵒᵖ ⥤ Ab.{u} :=
  (_root_.PresheafOfModules.toPresheaf (ringPresheaf O₂)).obj
    ((changeOfRings θ).obj ((_root_.PresheafOfModules.free (ringPresheaf O₁)).obj F))

variable (F : Cᵒᵖ ⥤ Type u)

/-- The tautological generator of the free presheaf of modules on a presheaf of sets `F`
attached to a section of `F` over an object of the site. -/
noncomputable def freeGenerator {R : Cᵒᵖ ⥤ RingCat.{u}} (F : Cᵒᵖ ⥤ Type u) (X : Cᵒᵖ)
    (s : F.obj X) : ((_root_.PresheafOfModules.free R).obj F).obj X :=
  ModuleCat.freeMk (R := R.obj X) s

/-- The restriction maps of the free presheaf of modules carry the generator attached to a
section to the generator attached to its restriction. -/
lemma freeGenerator_map {R : Cᵒᵖ ⥤ RingCat.{u}} (F : Cᵒᵖ ⥤ Type u) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (s : F.obj X) :
    (((_root_.PresheafOfModules.free R).obj F).map f).hom (freeGenerator F X s) =
      freeGenerator F Y (F.map f s) :=
  ModuleCat.freeDesc_apply _ _

/-- A multiple of the generator attached to a section of `F` is the function supported at that
section. -/
lemma smul_freeGenerator {R : Cᵒᵖ ⥤ RingCat.{u}} (F : Cᵒᵖ ⥤ Type u) (X : Cᵒᵖ) (s : F.obj X)
    (r : R.obj X) :
    r • freeGenerator F X s =
      (Finsupp.single s r : ((_root_.PresheafOfModules.free R).obj F).obj X) :=
  _root_.PresheafOfModules.smul_freeMk_eq_single r s

/-- The inclusion of the structure presheaf of `O₂` into the base change of the free presheaf of
modules on `F` as the summand indexed by a section `s` of `F`, namely `b ↦ b ⊗ s`. -/
noncomputable def changeOfRingsFreeSingleHom (X : Cᵒᵖ) (s : F.obj X) :
    (unitPresheaf O₂).obj X ⟶ (changeOfRingsFreePresheaf θ F).obj X :=
  letI := (θ.app X).hom.toAlgebra
  AddCommGrpCat.ofHom
    (show (O₂.obj X) →+ TensorProduct (O₁.obj X) (O₂.obj X)
        (((_root_.PresheafOfModules.free (ringPresheaf O₁)).obj F).obj X) from
      { toFun := fun b => b ⊗ₜ[O₁.obj X] (freeGenerator F X s)
        map_zero' := TensorProduct.zero_tmul _ _
        map_add' := fun a b => TensorProduct.add_tmul a b _ })

/-- `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsFreeSingleHom` on sections. -/
lemma changeOfRingsFreeSingleHom_apply (X : Cᵒᵖ) (s : F.obj X) (b : O₂.obj X) :
    letI := (θ.app X).hom.toAlgebra
    changeOfRingsFreeSingleHom θ F X s b = b ⊗ₜ[O₁.obj X] (freeGenerator F X s) :=
  rfl

open scoped Classical in
/-- The component of `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsFreeCopowerIso` at an
object of the site: the base change `O₂(X) ⊗_{O₁(X)} (F(X) →₀ O₁(X))` is `F(X) →₀ O₂(X)`, which
is the copower of `O₂(X)` by `F(X)`. -/
noncomputable def changeOfRingsFreeCopowerIsoApp (X : Cᵒᵖ) :
    ((unitPresheaf O₂).copower F).obj X ≅ (changeOfRingsFreePresheaf θ F).obj X :=
  letI := (θ.app X).hom.toAlgebra
  (AddCommGrpCat.finsuppCopowerIso ((unitPresheaf O₂).obj X) (F.obj X)).symm ≪≫
    (TensorProduct.finsuppScalarRight (O₁.obj X) (O₂.obj X) (O₂.obj X)
      (F.obj X)).symm.toAddEquiv.toAddCommGrpIso

/-- `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsFreeCopowerIsoApp` carries the summand
indexed by a section `s` of `F` to the tensors `b ⊗ s`. -/
@[reassoc]
lemma ι_changeOfRingsFreeCopowerIsoApp_hom (X : Cᵒᵖ) (s : F.obj X) :
    Sigma.ι (fun _ : F.obj X => (unitPresheaf O₂).obj X) s ≫
        (changeOfRingsFreeCopowerIsoApp θ F X).hom =
      changeOfRingsFreeSingleHom θ F X s := by
  classical
  let := (θ.app X).hom.toAlgebra
  have h : Sigma.ι (fun _ : F.obj X => (unitPresheaf O₂).obj X) s ≫
      (changeOfRingsFreeCopowerIsoApp θ F X).hom =
        AddCommGrpCat.ofHom (Finsupp.singleAddHom s) ≫
          ((TensorProduct.finsuppScalarRight (O₁.obj X) (O₂.obj X) (O₂.obj X)
            (F.obj X)).symm.toAddEquiv.toAddCommGrpIso).hom := by
    rw [changeOfRingsFreeCopowerIsoApp, Iso.trans_hom, Iso.symm_hom, ← Category.assoc,
      AddCommGrpCat.ι_finsuppCopowerIso_inv]
    rfl
  rw [h]
  ext (b : O₂.obj X)
  exact TensorProduct.finsuppScalarRight_symm_apply_single (R := O₁.obj X) (S := O₂.obj X) s b

/-- **The target half of the copower comparison: the base change of the free presheaf of modules
on a presheaf of sets `F` has underlying presheaf of abelian groups the copower of the structure
presheaf of the target by `F`.** Over each object this is Mathlib's
`TensorProduct.finsuppScalarRight`, `O₂(X) ⊗_{O₁(X)} (F(X) →₀ O₁(X)) = (F(X) →₀ O₂(X))`, and the
restriction maps permute the summands along those of `F`.

`PresheafOfModules.copowerFreeIso` is the source half, the same statement with no base change. -/
noncomputable def changeOfRingsFreeCopowerIso :
    (unitPresheaf O₂).copower F ≅ changeOfRingsFreePresheaf θ F :=
  NatIso.ofComponents (changeOfRingsFreeCopowerIsoApp θ F) (by
    intro X Y f
    apply Sigma.hom_ext
    intro s
    rw [Functor.copower_map, Sigma.ι_comp_map'_assoc, ι_changeOfRingsFreeCopowerIsoApp_hom,
      ι_changeOfRingsFreeCopowerIsoApp_hom_assoc]
    let := (θ.app X).hom.toAlgebra
    let := (θ.app Y).hom.toAlgebra
    ext (b : O₂.obj X)
    change ((O₂.map f).hom b) ⊗ₜ[O₁.obj Y] (freeGenerator F Y (F.map f s)) =
      (cofMap θ ((_root_.PresheafOfModules.free (ringPresheaf O₁)).obj F) f).hom
        (b ⊗ₜ[O₁.obj X] (freeGenerator F X s))
    rw [cofMap_tmul]
    congr 1
    exact (freeGenerator_map F f s).symm)

/-- The components of `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsFreeCopowerIso`. -/
@[simp]
lemma changeOfRingsFreeCopowerIso_hom_app (X : Cᵒᵖ) :
    (changeOfRingsFreeCopowerIso θ F).hom.app X = (changeOfRingsFreeCopowerIsoApp θ F X).hom :=
  rfl

/-- **The base-change unit at a free presheaf of modules**, read on underlying presheaves of
abelian groups: the component at `R⟨F⟩` of the unit of the change-of-rings adjunction,
`R⟨F⟩ ⟶ O₂ ⊗_{O₁} R⟨F⟩`, which is `m ↦ 1 ⊗ m` on sections. -/
noncomputable def freeUnit :
    (_root_.PresheafOfModules.toPresheaf (ringPresheaf O₁)).obj
        ((_root_.PresheafOfModules.free (ringPresheaf O₁)).obj F) ⟶
      changeOfRingsFreePresheaf θ F :=
  (Functor.whiskerRight (changeOfRingsAdjunction θ).unit
    (_root_.PresheafOfModules.toPresheaf (ringPresheaf O₁))).app
      ((_root_.PresheafOfModules.free (ringPresheaf O₁)).obj F)

/-- `Stacks.PresheafOfModules.ChangeOfRings.freeUnit` is `m ↦ 1 ⊗ m` on sections. -/
lemma freeUnit_app_apply (X : Cᵒᵖ)
    (m : ((_root_.PresheafOfModules.free (ringPresheaf O₁)).obj F).obj X) :
    letI := (θ.app X).hom.toAlgebra
    (freeUnit θ F).app X m = (1 : O₂.obj X) ⊗ₜ[O₁.obj X] m :=
  changeOfRingsAdjunction_unit_app_apply θ _ X m

/-- **On sections the base-change unit at a free presheaf of modules sends the function supported
at a section `s` of `F` with value `r` to `θ(r) ⊗ s`.** -/
lemma freeUnit_app_single (X : Cᵒᵖ) (s : F.obj X) (r : O₁.obj X) :
    letI := (θ.app X).hom.toAlgebra
    (freeUnit θ F).app X (Finsupp.single s r) =
      ((θ.app X).hom r) ⊗ₜ[O₁.obj X] (freeGenerator F X s) := by
  let := (θ.app X).hom.toAlgebra
  have h1 : (1 : O₂.obj X) ⊗ₜ[O₁.obj X]
        (r • freeGenerator (R := ringPresheaf O₁) F X s) =
      ((θ.app X).hom r) ⊗ₜ[O₁.obj X] (freeGenerator (R := ringPresheaf O₁) F X s) := by
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    change r • (1 : O₂.obj X) = (θ.app X).hom r
    rw [Algebra.smul_def, mul_one]
    rfl
  refine Eq.trans (freeUnit_app_apply θ F X (Finsupp.single s r)) (Eq.trans ?_ h1)
  exact congrArg (fun m : ((_root_.PresheafOfModules.free (ringPresheaf O₁)).obj F).obj X =>
    (1 : O₂.obj X) ⊗ₜ[O₁.obj X] m) (smul_freeGenerator (R := ringPresheaf O₁) F X s r).symm

/-- Evaluating an equation `f ≫ g = h` of morphisms of abelian groups at an element. -/
private lemma apply_comp_of_comp_eq {A B D : AddCommGrpCat.{u}} {f : A ⟶ B} {g : B ⟶ D}
    {h : A ⟶ D} (e : f ≫ g = h) (x : A) : g (f x) = h x := by
  rw [← e]
  rfl

/-- **The square identifying the base-change unit at a free presheaf of modules with the copower
of the augmentation.** Under `PresheafOfModules.copowerFreeIso` and
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsFreeCopowerIso`, the unit
`R⟨F⟩ ⟶ O₂ ⊗_{O₁} R⟨F⟩` of the change-of-rings adjunction at a free presheaf of modules is the
copower by `F` of the map of structure presheaves underlying `θ`. On sections, on the summand
indexed by a section `s` of `F`, both sides send `r` to `θ(r) ⊗ s`. -/
lemma copowerFreeIso_unitMap_copowerMap :
    Functor.copowerMap (unitMap θ) (𝟙 F) ≫ (changeOfRingsFreeCopowerIso θ F).hom =
      (_root_.PresheafOfModules.copowerFreeIso (ringPresheaf O₁) F).hom ≫ freeUnit θ F := by
  apply NatTrans.ext
  funext X
  apply Sigma.hom_ext
  intro s
  let := (θ.app X).hom.toAlgebra
  ext r
  have hL : (Functor.copowerMap (unitMap θ) (𝟙 F)).app X
        (Sigma.ι (fun _ : F.obj X => (unitPresheaf O₁).obj X) s r) =
      Sigma.ι (fun _ : F.obj X => (unitPresheaf O₂).obj X) s ((unitMap θ).app X r) :=
    apply_comp_of_comp_eq (Functor.ι_copowerMap_app (unitMap θ) (𝟙 F) X s) r
  have hR : (_root_.PresheafOfModules.copowerFreeIso (ringPresheaf O₁) F).hom.app X
        (Sigma.ι (fun _ : F.obj X => (unitPresheaf O₁).obj X) s r) =
      Finsupp.single s r :=
    apply_comp_of_comp_eq
      (_root_.PresheafOfModules.ι_copowerFreeIsoApp_hom (ringPresheaf O₁) F X s) r
  have hι : (changeOfRingsFreeCopowerIso θ F).hom.app X
        (Sigma.ι (fun _ : F.obj X => (unitPresheaf O₂).obj X) s ((unitMap θ).app X r)) =
      ((θ.app X).hom r) ⊗ₜ[O₁.obj X] (freeGenerator F X s) :=
    apply_comp_of_comp_eq (ι_changeOfRingsFreeCopowerIsoApp_hom θ F X s) _
  simp only [NatTrans.comp_app, CategoryTheory.comp_apply]
  rw [hL, hι, hR]
  exact (freeUnit_app_single θ F X s r).symm

end Stacks.PresheafOfModules.ChangeOfRings

/-! ### Quasi-isomorphisms of reindexed Moore complexes -/

namespace AlgebraicTopology

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- **A map of simplicial objects is a quasi-isomorphism on the reindexed Moore complexes
exactly when the homology of the Moore complex inverts it in every degree.** The reindexing
along `ComplexShape.embeddingUpIntLE 0` changes no homology group, and the cochain complex
vanishes outside the image of that embedding. -/
lemma quasiIso_alternatingFaceMapCochainComplex_map_iff {P P' : SimplicialObject A} (f : P ⟶ P') :
    QuasiIso ((alternatingFaceMapCochainComplex A).map f) ↔
      ∀ n : ℕ, IsIso ((Stacks.ChaoticSite.mooreHomologyFunctor A n).map f) := by
  have h : QuasiIso ((alternatingFaceMapCochainComplex A).map f) ↔
      QuasiIso ((alternatingFaceMapComplex A).map f) :=
    HomologicalComplex.quasiIso_extendMap_iff ((alternatingFaceMapComplex A).map f)
      (ComplexShape.embeddingUpIntLE (0 : ℤ))
  rw [h, quasiIso_iff]
  exact forall_congr' fun n => quasiIsoAt_iff_isIso_homologyMap _ n

/-- **A map of simplicial objects which is a quasi-isomorphism on Moore complexes stays one
after multiplication by a contractible simplicial set.** Here `S` is given together with a
homotopy equivalence `a : S ⟶ ∗` onto the constant simplicial set on a singleton, and the
product `S × P` is the copower `CategoryTheory.Functor.copower`.

This is `Stacks.ChaoticSite.isIso_mooreHomologyFunctor_map_copowerMap` read on the reindexed
Moore complex, which is the form in which the base-change unit of a simplicial module is
stated. -/
theorem quasiIso_alternatingFaceMapCochainComplex_map_copowerMap
    {P P' : SimplicialObject A} (ψ : P ⟶ P') {S : SimplicialObject (Type w)}
    {a : S ⟶ (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{w + 1}}
    [∀ j, HasCoproduct fun _ : S.obj j => P.obj j]
    [∀ j, HasCoproduct fun _ : S.obj j => P'.obj j]
    [∀ j, HasCoproduct
      fun _ : ((Functor.const SimplexCategoryᵒᵖ).obj PUnit.{w + 1}).obj j => P.obj j]
    [∀ j, HasCoproduct
      fun _ : ((Functor.const SimplexCategoryᵒᵖ).obj PUnit.{w + 1}).obj j => P'.obj j]
    (ha : SimplicialObject.homotopyEquivalences (Type w) a)
    (hψ : QuasiIso ((alternatingFaceMapCochainComplex A).map ψ)) :
    QuasiIso ((alternatingFaceMapCochainComplex A).map (Functor.copowerMap ψ (𝟙 S))) := by
  rw [quasiIso_alternatingFaceMapCochainComplex_map_iff] at hψ ⊢
  exact fun n => Stacks.ChaoticSite.isIso_mooreHomologyFunctor_map_copowerMap ψ ha n (hψ n)

/-- **The reindexed Moore complex preserves colimits.** Colimits of complexes are computed
degreewise, and in each cohomological degree the reindexed Moore complex is either an evaluation
of the simplicial object (`AlgebraicTopology.alternatingFaceMapCochainComplexCompEvalIso`) or
zero. -/
instance preservesColimitsOfShape_alternatingFaceMapCochainComplex
    {J : Type*} [Category* J] [HasColimitsOfShape J A] :
    PreservesColimitsOfShape J (alternatingFaceMapCochainComplex A) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun q => by
    by_cases hq : ∃ n : ℕ, (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = q
    · obtain ⟨n, rfl⟩ := hq
      exact preservesColimitsOfShape_of_natIso
        (alternatingFaceMapCochainComplexCompEvalIso A n).symm
    · exact Functor.preservesColimitsOfShape_of_isZero _
        (Functor.isZero _ (fun _ => HomologicalComplex.isZero_extend_X _ _ q (by tauto))) _)

end AlgebraicTopology

/-! ### AB4 for quasi-isomorphisms of cochain complexes -/

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A] {I : Type w}

/-- **A family of cochain complexes read as a single cochain complex of diagrams** indexed by
the discrete category on the index type. Its degreewise colimit is the coproduct of the family,
which is `CochainComplex.sigmaIsoDiscreteFamily`. -/
abbrev discreteFamily (K : I → CochainComplex A ℤ) : CochainComplex (Discrete I ⥤ A) ℤ where
  X n := Discrete.functor (fun i => (K i).X n)
  d n m := Discrete.natTrans (fun i => (K i.as).d n m)
  shape n m h := by
    refine NatTrans.ext (funext fun i => ?_)
    exact (K i.as).shape n m h
  d_comp_d' n m k _ _ := by
    refine NatTrans.ext (funext fun i => ?_)
    exact (K i.as).d_comp_d n m k

/-- A family of morphisms of cochain complexes read as a morphism between the cochain complexes
of diagrams of `CochainComplex.discreteFamily`. -/
abbrev discreteFamilyMap {K L : I → CochainComplex A ℤ} (f : ∀ i, K i ⟶ L i) :
    discreteFamily K ⟶ discreteFamily L where
  f n := Discrete.natTrans (fun i => (f i.as).f n)
  comm' n m _ := by
    refine NatTrans.ext (funext fun i => ?_)
    exact (f i.as).comm n m

/-- Evaluating `CochainComplex.discreteFamilyMap` at an index gives back the member of the
family. -/
lemma mapHomologicalComplex_evaluation_discreteFamilyMap
    {K L : I → CochainComplex A ℤ} (f : ∀ i, K i ⟶ L i) (i : I) :
    (((evaluation (Discrete I) A).obj ⟨i⟩).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (discreteFamilyMap f) = f i :=
  rfl

variable [HasColimitsOfShape (Discrete I) A]

/-- The injection of a member of the family into the degreewise colimit of
`CochainComplex.discreteFamily`. -/
abbrev discreteFamilyι (K : I → CochainComplex A ℤ) (i : I) :
    K i ⟶ ((colim : (Discrete I ⥤ A) ⥤ A).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (discreteFamily K) where
  f n := colimit.ι ((discreteFamily K).X n) ⟨i⟩
  comm' n m _ := ι_colimMap ((discreteFamily K).d n m) ⟨i⟩

/-- The degreewise colimit of `CochainComplex.discreteFamily`, as a cocone on the family. -/
abbrev discreteFamilyCocone (K : I → CochainComplex A ℤ) : Cocone (Discrete.functor K) where
  pt := ((colim : (Discrete I ⥤ A) ⥤ A).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj (discreteFamily K)
  ι := Discrete.natTrans (fun i => discreteFamilyι K i.as)

/-- **`CochainComplex.discreteFamilyCocone` is a colimit cocone**: in each cohomological degree
it is the colimit of the degrees, because colimits of complexes are computed degreewise. -/
def isColimitDiscreteFamilyCocone (K : I → CochainComplex A ℤ) :
    IsColimit (discreteFamilyCocone K) where
  desc t :=
    { f := fun n => colimit.desc ((discreteFamily K).X n)
        { pt := t.pt.X n
          ι := Discrete.natTrans (fun i => (t.ι.app i).f n) }
      comm' := fun n m _ => by
        refine colimit.hom_ext (fun i => ?_)
        have h1 : colimit.ι ((discreteFamily K).X n) i ≫ (discreteFamilyCocone K).pt.d n m =
            ((discreteFamily K).d n m).app i ≫ colimit.ι ((discreteFamily K).X m) i := by
          apply ι_colimMap
        rw [← Category.assoc, colimit.ι_desc, ← Category.assoc, h1, Category.assoc,
          colimit.ι_desc]
        exact (t.ι.app i).comm n m }
  fac t j := by
    refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
    exact colimit.ι_desc _ j
  uniq t m hm := by
    refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
    refine colimit.hom_ext (fun i => ?_)
    rw [colimit.ι_desc]
    exact congrArg (fun φ => HomologicalComplex.Hom.f φ n) (hm i)

/-- **The coproduct of a family of cochain complexes is the degreewise colimit of the
corresponding complex of diagrams.** -/
def sigmaIsoDiscreteFamily (K : I → CochainComplex A ℤ) :
    (∐ K) ≅ ((colim : (Discrete I ⥤ A) ⥤ A).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (discreteFamily K) :=
  (colimit.isColimit (Discrete.functor K)).coconePointUniqueUpToIso
    (isColimitDiscreteFamilyCocone K)

/-- `CochainComplex.sigmaIsoDiscreteFamily` matches the two families of injections. -/
@[reassoc]
lemma ι_sigmaIsoDiscreteFamily_hom (K : I → CochainComplex A ℤ) (i : I) :
    Sigma.ι K i ≫ (sigmaIsoDiscreteFamily K).hom = discreteFamilyι K i :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit (Discrete.functor K))
    (isColimitDiscreteFamilyCocone K) ⟨i⟩

/-- `CochainComplex.sigmaIsoDiscreteFamily` identifies the coproduct of a family of morphisms
with the degreewise colimit of the corresponding morphism of complexes of diagrams. -/
lemma sigmaMap_comp_sigmaIsoDiscreteFamily_hom {K L : I → CochainComplex A ℤ}
    (f : ∀ i, K i ⟶ L i) :
    Limits.Sigma.map f ≫ (sigmaIsoDiscreteFamily L).hom =
      (sigmaIsoDiscreteFamily K).hom ≫
        ((colim : (Discrete I ⥤ A) ⥤ A).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (discreteFamilyMap f) := by
  refine Limits.Sigma.hom_ext _ _ (fun i => ?_)
  rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, ι_sigmaIsoDiscreteFamily_hom,
    ι_sigmaIsoDiscreteFamily_hom_assoc]
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  exact (ι_colimMap ((discreteFamilyMap f).f n) ⟨i⟩).symm

/-- **Grothendieck's axiom AB4 for quasi-isomorphisms: a coproduct of quasi-isomorphisms of
cochain complexes is a quasi-isomorphism**, as soon as coproducts of that shape are exact. The
coproduct is the degreewise colimit of the corresponding complex of diagrams
(`CochainComplex.sigmaIsoDiscreteFamily`), exactness of the colimit makes it preserve homology,
and a quasi-isomorphism of complexes of diagrams is one after evaluation at every index. -/
theorem quasiIso_sigmaMap [HasFiniteLimits A] [HasExactColimitsOfShape (Discrete I) A]
    {K L : I → CochainComplex A ℤ} (f : ∀ i, K i ⟶ L i) (hf : ∀ i, QuasiIso (f i)) :
    QuasiIso (Limits.Sigma.map f) := by
  have _hpres : (colim (J := Discrete I) (C := A)).PreservesHomology := by
    have : PreservesFiniteLimits (colim (J := Discrete I) (C := A)) := inferInstance
    have : PreservesColimitsOfSize.{0, 0} (colim (J := Discrete I) (C := A)) :=
      (colimConstAdj (J := Discrete I) (C := A)).leftAdjoint_preservesColimits
    have : PreservesFiniteColimits (colim (J := Discrete I) (C := A)) :=
      PreservesColimitsOfSize.preservesFiniteColimits _
    infer_instance
  have _hq : QuasiIso (discreteFamilyMap f) := by
    rw [HomologicalComplex.quasiIso_iff_evaluation]
    intro i
    exact hf i.as
  have key : Limits.Sigma.map f = (sigmaIsoDiscreteFamily K).hom ≫
      ((colim : (Discrete I ⥤ A) ⥤ A).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (discreteFamilyMap f) ≫ (sigmaIsoDiscreteFamily L).inv := by
    rw [← Category.assoc, ← sigmaMap_comp_sigmaIsoDiscreteFamily_hom, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [key]
  infer_instance

/-- **A natural transformation between functors to cochain complexes which preserve coproducts
is a quasi-isomorphism at a coproduct as soon as it is one at every summand.** The comparison
maps `∐ T(N i) ⟶ T(∐ N)` are invertible, and a coproduct of quasi-isomorphisms is a
quasi-isomorphism (`CochainComplex.quasiIso_sigmaMap`). -/
theorem quasiIso_app_sigma [HasFiniteLimits A]
    [HasExactColimitsOfShape (Discrete I) A] {D : Type*} [Category* D]
    {T₁ T₂ : D ⥤ CochainComplex A ℤ} (η : T₁ ⟶ T₂)
    [PreservesColimitsOfShape (Discrete I) T₁] [PreservesColimitsOfShape (Discrete I) T₂]
    (N : I → D) [HasCoproduct N] (h : ∀ i, QuasiIso (η.app (N i))) :
    QuasiIso (η.app (∐ N)) := by
  have hsq : sigmaComparison T₁ N ≫ η.app (∐ N) =
      Limits.Sigma.map (fun i => η.app (N i)) ≫ sigmaComparison T₂ N := by
    refine Limits.Sigma.hom_ext _ _ (fun i => ?_)
    rw [← Category.assoc, ι_comp_sigmaComparison, ← Category.assoc, Limits.Sigma.ι_map,
      Category.assoc, ι_comp_sigmaComparison]
    exact η.naturality (Sigma.ι N i)
  have _hs : QuasiIso (Limits.Sigma.map (fun i => η.app (N i))) := quasiIso_sigmaMap _ h
  have _hc : QuasiIso (sigmaComparison T₁ N ≫ η.app (∐ N)) := by
    rw [hsq]; infer_instance
  exact quasiIso_of_comp_left (sigmaComparison T₁ N) (η.app (∐ N))

end CochainComplex

/-! ### Simplicial modules and the base-change unit on Moore complexes -/

namespace Stacks.SimplicialModules

open Stacks.PresheafOfModules.ChangeOfRings

/-- **Simplicial modules over the simplicial commutative ring `O`**: presheaves of modules on
`Δ` over the presheaf of rings underlying `O`. The chaotic topology on `Δ` is invisible here,
every presheaf on `Δ` being a sheaf for it, which is the simplification Remark
[Stacks, Tag 08QD] records. -/
abbrev SMod (O : SimplexCategoryᵒᵖ ⥤ CommRingCat.{u}) : Type (u + 1) :=
  PresheafOfModules.{u} (ringPresheaf O)

/-- **`s(-)`: the Moore complex of the underlying simplicial abelian group of a simplicial
module**, read as a cochain complex over `ℤ` with simplicial degree `n` in cohomological
degree `-n`. -/
abbrev mooreCochain (O : SimplexCategoryᵒᵖ ⥤ CommRingCat.{u}) :
    SMod O ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  PresheafOfModules.toPresheaf (ringPresheaf O) ⋙
    alternatingFaceMapCochainComplex AddCommGrpCat.{u}

variable {O : SimplexCategoryᵒᵖ ⥤ CommRingCat.{u}} {B : CommRingCat.{u}}
  (φ : O ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)

/-- **The base-change unit read on Moore complexes**, `s(Q_•) ⟶ s(Q_• ⊗_{O_•} B̲)`: the unit of
the change-of-rings adjunction `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction`
along the augmentation `φ`, whiskered onto underlying presheaves of abelian groups and then onto
Moore complexes.

The Δ-instance of [Stacks, Tag 08RX] asserts that this is a quasi-isomorphism at every
degreewise flat simplicial `O`-module as soon as it is one at
`PresheafOfModules.unit (ringPresheaf O)`, which is the statement `O ⊗_O B = B̲`; see the
implementation notes of this module for what is proved towards it. -/
def mooreCochainBaseChange :
    mooreCochain O ⟶ changeOfRings φ ⋙ mooreCochain ((Functor.const SimplexCategoryᵒᵖ).obj B) :=
  Functor.whiskerRight
    (Functor.whiskerRight (changeOfRingsAdjunction φ).unit
      (PresheafOfModules.toPresheaf (ringPresheaf O)))
    (alternatingFaceMapCochainComplex AddCommGrpCat.{u})

/-- Degreewise, base change along `φ` is Mathlib's extension of scalars. This holds by
definition, and is what lets the row direction of the intended proof consume flatness through
`CochainComplex.DerivedTensor.KFlatDerived.quasiIso_extendScalars_map_of_kFlat`. -/
lemma changeOfRings_obj_obj (M : SMod O) (n : SimplexCategoryᵒᵖ) :
    ((changeOfRings φ).obj M).obj n =
      (ModuleCat.extendScalars (R := O.obj n) (S := B) (φ.app n).hom).obj (M.obj n) :=
  rfl

/-- **The base-change unit is a quasi-isomorphism at a free simplicial module on a contractible
simplicial set**, as soon as it is one on the underlying simplicial abelian groups of the
augmentation itself. This is the column step of the Δ-instance of [Stacks, Tag 08RX]: the
underlying simplicial abelian group of `O⟨F⟩` is the product of `F` with `O_•`
(`PresheafOfModules.copowerFreeIso`), that of its base change is the product of `F` with `B̲`
(`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsFreeCopowerIso`), the unit is the product of
`F` with the augmentation
(`Stacks.PresheafOfModules.ChangeOfRings.copowerFreeIso_unitMap_copowerMap`), and multiplying by a
contractible simplicial set does not change which maps the homology of the Moore complex inverts
(`AlgebraicTopology.quasiIso_alternatingFaceMapCochainComplex_map_copowerMap`).

Here `F` is given together with a homotopy equivalence `a : F ⟶ ∗` onto the constant simplicial
set on a singleton; at `F = Δ[m]` such an `a` is
`SSet.stdSimplex.homotopyEquivalences_hom_obj₀`. -/
theorem quasiIso_mooreCochainBaseChange_app_free {F : SimplexCategoryᵒᵖ ⥤ Type u}
    {a : F ⟶ (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1}}
    (ha : SimplicialObject.homotopyEquivalences (Type u) a)
    (hφ : QuasiIso ((alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map (unitMap φ))) :
    QuasiIso ((mooreCochainBaseChange φ).app
      ((PresheafOfModules.free (ringPresheaf O)).obj F)) := by
  have hcop : QuasiIso ((alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map
      (Functor.copowerMap (unitMap φ) (𝟙 F))) :=
    quasiIso_alternatingFaceMapCochainComplex_map_copowerMap _ ha hφ
  have key : (mooreCochainBaseChange φ).app ((PresheafOfModules.free (ringPresheaf O)).obj F) =
      (alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map
        ((PresheafOfModules.copowerFreeIso (ringPresheaf O) F).inv ≫
          Functor.copowerMap (unitMap φ) (𝟙 F) ≫ (changeOfRingsFreeCopowerIso φ F).hom) := by
    rw [copowerFreeIso_unitMap_copowerMap, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rfl
  rw [key, Functor.map_comp, Functor.map_comp]
  infer_instance

/-- **The standard zero-simplex is the constant simplicial set on a singleton**: every object
of `Δ` has exactly one morphism to `⦋0⦌`. -/
def stdSimplexZeroIsoConst :
    (SSet.stdSimplex.{u}).obj (SimplexCategory.mk 0) ≅
      (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1} :=
  NatIso.ofComponents (fun x =>
      Equiv.toIso (Equiv.ulift.trans (Equiv.equivPUnit (x.unop ⟶ SimplexCategory.mk 0))))
    (by intros; ext; rfl)

/-- **The base-change unit is a quasi-isomorphism at the free simplicial module on a standard
simplex**, the standard simplices being contractible ([Stacks, Tag 08QD]). -/
theorem quasiIso_mooreCochainBaseChange_app_freeStdSimplex (m : SimplexCategory)
    (hφ : QuasiIso ((alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map (unitMap φ))) :
    QuasiIso ((mooreCochainBaseChange φ).app
      ((PresheafOfModules.free (ringPresheaf O)).obj ((SSet.stdSimplex.{u}).obj m))) :=
  quasiIso_mooreCochainBaseChange_app_free φ
    (SimplicialObject.homotopyEquivalences_iso_comp_iso (Iso.refl _)
      ((SSet.stdSimplex.{u}).map (default : m ⟶ SimplexCategory.mk 0)) stdSimplexZeroIsoConst
      ((SSet.stdSimplex.homotopyEquivalences_hom_obj₀ m.len).1 _)) hφ

/-- **The column step of the Δ-instance of [Stacks, Tag 08RX]: the base-change unit is a
quasi-isomorphism at the canonical cover of any simplicial module by free simplicial modules on
standard simplices.** The cover is a coproduct, indexed by the sections of `M`, of free
simplicial modules on standard simplices (`PresheafOfModules.stdCover`); the base-change unit is
a quasi-isomorphism at each summand by
`Stacks.SimplicialModules.quasiIso_mooreCochainBaseChange_app_freeStdSimplex`, both sides take
coproducts to coproducts, and a coproduct of quasi-isomorphisms of cochain complexes of abelian
groups is a quasi-isomorphism (`CochainComplex.quasiIso_sigmaMap`, Grothendieck's AB4). -/
theorem quasiIso_mooreCochainBaseChange_app_stdCover (M : SMod O)
    (hφ : QuasiIso ((alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map (unitMap φ))) :
    QuasiIso ((mooreCochainBaseChange φ).app M.stdCover) :=
  CochainComplex.quasiIso_app_sigma (mooreCochainBaseChange φ) _
    (fun m => quasiIso_mooreCochainBaseChange_app_freeStdSimplex φ m.1.unop hφ)

end Stacks.SimplicialModules

/-! ### The same machinery over a base category in an arbitrary universe

The free presheaf of modules on a universe-lifted representable, the standard cover, and the
copower descriptions of the free presheaf and of its base change, for a small category `C` whose
objects live in an arbitrary universe `u₀`, the ring, module and index universes being max'd
against it. This is what the simplicial site `Δ × C` of Stacks 09D0 needs; at `u₀ = 0` it is
the statement above. The declarations carry the names of their `Type`-based counterparts with a
prime. -/

universe u₀

namespace PresheafOfModules

variable {C : Type u₀} [SmallCategory C] {R : Cᵒᵖ ⥤ RingCat.{max u₀ u}}

/-- **Maps out of the free presheaf of modules on a universe-lifted representable are the
sections over the representing object.** This is `PresheafOfModules.freeYonedaEquiv` with
`CategoryTheory.yoneda` replaced by `CategoryTheory.uliftYoneda`, which is what makes it
available when the hom universe of `C` is smaller than the universe of the presheaf of rings. -/
def freeUliftYonedaEquiv' {M : PresheafOfModules.{max u₀ u} R} {X : C} :
    ((free R).obj (uliftYoneda.{u}.obj X) ⟶ M) ≃ M.obj (op X) :=
  freeHomEquiv.trans uliftYonedaEquiv

/-- `PresheafOfModules.freeUliftYonedaEquiv'` evaluates a map at the tautological generator. -/
lemma freeUliftYonedaEquiv_apply' {M : PresheafOfModules.{max u₀ u} R} {X : C}
    (ψ : (free R).obj (uliftYoneda.{u}.obj X) ⟶ M) :
    freeUliftYonedaEquiv' ψ = ψ.app (op X) (ModuleCat.freeMk (ULift.up (𝟙 X))) :=
  rfl

/-- `PresheafOfModules.freeUliftYonedaEquiv'` is natural in the target. -/
lemma freeUliftYonedaEquiv_comp' {M N : PresheafOfModules.{max u₀ u} R} {X : C}
    (m : (free R).obj (uliftYoneda.{u}.obj X) ⟶ M) (φ : M ⟶ N) :
    freeUliftYonedaEquiv' (m ≫ φ) = φ.app _ (freeUliftYonedaEquiv' m) :=
  rfl

/-- The map attached to a section carries the tautological generator to that section. -/
lemma freeUliftYonedaEquiv_symm_app' (M : PresheafOfModules.{max u₀ u} R) (X : C)
    (x : M.obj (op X)) :
    (freeUliftYonedaEquiv'.symm x).app (op X) (ModuleCat.freeMk (ULift.up (𝟙 X))) = x := by
  rw [← freeUliftYonedaEquiv_apply', Equiv.apply_symm_apply]

/-- **The free presheaf of modules on a universe-lifted representable is projective.** Maps out
of it are the sections over the representing object, and an epimorphism of presheaves of modules
is surjective on sections. -/
@[sga "4 V 2.3.1"]
instance uliftFreeYonedaProjective' (X : C) :
    Projective ((free R).obj (uliftYoneda.{u}.obj X)) where
  factors {_ _} g e he := by
    have := he
    obtain ⟨y, hy⟩ := surjective_of_epi e (op X) (freeUliftYonedaEquiv' g)
    exact ⟨freeUliftYonedaEquiv'.symm y, freeUliftYonedaEquiv'.injective <| by
      rwa [freeUliftYonedaEquiv_comp', Equiv.apply_symm_apply]⟩

/-- The coproduct, indexed by the sections of `M`, of the free presheaves of modules on the
universe-lifted representables. At `C = Δ` the summands are the free presheaves of modules on
the standard simplices, `SSet.stdSimplex` being `CategoryTheory.uliftYoneda` by definition. -/
abbrev stdCover' (M : PresheafOfModules.{max u₀ u} R) : PresheafOfModules.{max u₀ u} R :=
  ∐ (fun m : M.Elements => (free R).obj (uliftYoneda.{u}.obj m.1.unop))

/-- The canonical map `PresheafOfModules.stdCover' M ⟶ M`, given on the summand indexed by a
section by the map that section corresponds to under
`PresheafOfModules.freeUliftYonedaEquiv'`. -/
def fromStdCover' (M : PresheafOfModules.{max u₀ u} R) : M.stdCover' ⟶ M :=
  Sigma.desc (fun m => freeUliftYonedaEquiv'.symm m.2)

/-- **`PresheafOfModules.fromStdCover'` is an epimorphism**: the summand indexed by a section
already hits that section. -/
instance epi_fromStdCover' (M : PresheafOfModules.{max u₀ u} R) : Epi M.fromStdCover' := by
  refine epi_of_surjective (fun X x => ⟨?_, ?_⟩)
  · exact (Sigma.ι (fun m : M.Elements =>
      (free R).obj (uliftYoneda.{u}.obj m.1.unop)) (M.elementsMk X x)).app X
      (ModuleCat.freeMk (ULift.up (𝟙 X.unop)))
  · have h := ConcreteCategory.congr_hom
      ((evaluation R X ⋙ forget _).congr_map
        (Sigma.ι_comp_desc (fun m : M.Elements => freeUliftYonedaEquiv'.symm m.2)
          (M.elementsMk X x))) (ModuleCat.freeMk (ULift.up (𝟙 X.unop)))
    exact h.trans (freeUliftYonedaEquiv_symm_app' M X.unop x)

/-- **Presheaves of modules over a presheaf of rings on a category whose objects and morphisms
form types in `Type 0` have enough projectives**, with no constraint relating the universe of
the rings to the site: every presheaf of modules receives an epimorphism from
`PresheafOfModules.stdCover'`, a coproduct of free presheaves of modules on the universe-lifted
representables, and those are projective.

`PresheafOfModules.enoughProjectives` is the same statement for a site whose universe equals
that of the rings, which is the generality Mathlib's Yoneda presentation offers. -/
instance enoughProjectives_of_smallType' : EnoughProjectives (PresheafOfModules.{max u₀ u} R) :=
  ⟨fun M => ⟨{ p := M.stdCover', f := M.fromStdCover' }⟩⟩

end PresheafOfModules

namespace PresheafOfModules

variable {C : Type u₀} [SmallCategory C] (R : Cᵒᵖ ⥤ RingCat.{max u₀ u}) (F : Cᵒᵖ ⥤ Type (max u₀ u))

/-- The inclusion of the structure presheaf into the free presheaf of modules on `F` as the
summand indexed by a section `s` of `F`, read on underlying presheaves of abelian groups. -/
def freeSingleHom' (X : Cᵒᵖ) (s : F.obj X) :
    ((toPresheaf R).obj (PresheafOfModules.unit R)).obj X ⟶
      ((toPresheaf R).obj ((free R).obj F)).obj X :=
  AddCommGrpCat.ofHom (Finsupp.singleAddHom s)

/-- The component of `PresheafOfModules.copowerFreeIso'` at an object of the site. -/
def copowerFreeIsoApp' (X : Cᵒᵖ) :
    (((toPresheaf R).obj (PresheafOfModules.unit R)).copower F).obj X ≅
      ((toPresheaf R).obj ((free R).obj F)).obj X :=
  (AddCommGrpCat.finsuppCopowerIso
    (((toPresheaf R).obj (PresheafOfModules.unit R)).obj X) (F.obj X)).symm

/-- `PresheafOfModules.copowerFreeIsoApp'` carries the summand indexed by a section `s` to its
image under `PresheafOfModules.freeSingleHom'`. -/
@[reassoc]
lemma ι_copowerFreeIsoApp_hom' (X : Cᵒᵖ) (s : F.obj X) :
    Sigma.ι (fun _ : F.obj X => ((toPresheaf R).obj (PresheafOfModules.unit R)).obj X) s ≫
      (copowerFreeIsoApp' R F X).hom = freeSingleHom' R F X s :=
  AddCommGrpCat.ι_finsuppCopowerIso_inv _ _ s

/-- The summand inclusions of `PresheafOfModules.freeSingleHom'` are compatible with the
restriction maps: restricting and then including at the restricted index agrees with including
and then restricting. -/
lemma freeSingleHom_naturality' {X Y : Cᵒᵖ} (f : X ⟶ Y) (s : F.obj X) :
    ((toPresheaf R).obj (PresheafOfModules.unit R)).map f ≫ freeSingleHom' R F Y (F.map f s) =
      freeSingleHom' R F X s ≫ ((toPresheaf R).obj ((free R).obj F)).map f :=
  single_comp_map_free R F f s

/-- **The underlying presheaf of abelian groups of the free presheaf of modules on a presheaf of
sets `F` is the copower of the structure presheaf by `F`.** Over each object the free module on
`F(X)` is the direct sum of `F(X)`-many copies of `R(X)`, and the restriction maps of the free
presheaf of modules permute the summands along those of `F`. -/
def copowerFreeIso' :
    ((toPresheaf R).obj (PresheafOfModules.unit R)).copower F ≅
      (toPresheaf R).obj ((free R).obj F) :=
  NatIso.ofComponents (copowerFreeIsoApp' R F) fun f => Sigma.hom_ext _ _ fun s => by
    rw [Functor.copower_map, Sigma.ι_comp_map'_assoc, ι_copowerFreeIsoApp_hom',
      ι_copowerFreeIsoApp_hom'_assoc]
    exact freeSingleHom_naturality' R F f s

end PresheafOfModules

namespace Stacks.PresheafOfModules.ChangeOfRings

open scoped TensorProduct

variable {C : Type u₀} [SmallCategory C] (O : Cᵒᵖ ⥤ CommRingCat.{max u₀ u})

/-- The presheaf of abelian groups underlying the structure presheaf of modules of a presheaf of
commutative rings. At `C = Δ` this is the simplicial abelian group underlying a simplicial
commutative ring. -/
abbrev unitPresheaf' : Cᵒᵖ ⥤ Ab.{max u₀ u} :=
  (_root_.PresheafOfModules.toPresheaf (ringPresheaf O)).obj
    (_root_.PresheafOfModules.unit (ringPresheaf O))

variable {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{max u₀ u}} (θ : O₁ ⟶ O₂)

/-- **A morphism of presheaves of commutative rings read on the underlying presheaves of abelian
groups of the two structure presheaves of modules**: `θ` itself, with the multiplicative
structure forgotten. At `C = Δ` this is the map of simplicial abelian groups
`s(O_•) ⟶ s(O'_•)` underlying a homomorphism of simplicial rings. -/
def unitMap' : unitPresheaf' O₁ ⟶ unitPresheaf' O₂ where
  app X := AddCommGrpCat.ofHom (θ.app X).hom.toAddMonoidHom
  naturality X Y f := by
    ext (r : O₁.obj X)
    exact congrArg (fun g => CommRingCat.Hom.hom g r) (θ.naturality f)

/-- `Stacks.PresheafOfModules.ChangeOfRings.unitMap'` is `θ` on sections. -/
lemma unitMap_app_apply' (X : Cᵒᵖ) (r : O₁.obj X) :
    (unitMap' θ).app X r = (θ.app X).hom r :=
  rfl

/-- **Base change of presheaves of modules preserves colimits**, being a left adjoint
(`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction`). -/
instance isLeftAdjoint_changeOfRings' :
    Functor.IsLeftAdjoint (changeOfRings θ : _root_.PresheafOfModules.{max u₀ u} (ringPresheaf O₁) ⥤
      _root_.PresheafOfModules.{max u₀ u} (ringPresheaf O₂)) :=
  ⟨_, ⟨changeOfRingsAdjunction θ⟩⟩

/-- The presheaf of abelian groups underlying the base change along `θ` of the free presheaf of
`O₁`-modules on a presheaf of sets. -/
abbrev changeOfRingsFreePresheaf' (F : Cᵒᵖ ⥤ Type (max u₀ u)) : Cᵒᵖ ⥤ Ab.{max u₀ u} :=
  (_root_.PresheafOfModules.toPresheaf (ringPresheaf O₂)).obj
    ((changeOfRings θ).obj ((_root_.PresheafOfModules.free (ringPresheaf O₁)).obj F))

variable (F : Cᵒᵖ ⥤ Type (max u₀ u))

/-- The tautological generator of the free presheaf of modules on a presheaf of sets `F`
attached to a section of `F` over an object of the site. -/
noncomputable def freeGenerator' {R : Cᵒᵖ ⥤ RingCat.{max u₀ u}} (F : Cᵒᵖ ⥤ Type (max u₀ u))
    (X : Cᵒᵖ) (s : F.obj X) : ((_root_.PresheafOfModules.free R).obj F).obj X :=
  ModuleCat.freeMk (R := R.obj X) s

/-- The restriction maps of the free presheaf of modules carry the generator attached to a
section to the generator attached to its restriction. -/
lemma freeGenerator_map' {R : Cᵒᵖ ⥤ RingCat.{max u₀ u}} (F : Cᵒᵖ ⥤ Type (max u₀ u)) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) (s : F.obj X) :
    (((_root_.PresheafOfModules.free R).obj F).map f).hom (freeGenerator' F X s) =
      freeGenerator' F Y (F.map f s) :=
  ModuleCat.freeDesc_apply _ _

/-- A multiple of the generator attached to a section of `F` is the function supported at that
section. -/
lemma smul_freeGenerator' {R : Cᵒᵖ ⥤ RingCat.{max u₀ u}} (F : Cᵒᵖ ⥤ Type (max u₀ u)) (X : Cᵒᵖ)
    (s : F.obj X) (r : R.obj X) :
    r • freeGenerator' F X s =
      (Finsupp.single s r : ((_root_.PresheafOfModules.free R).obj F).obj X) :=
  _root_.PresheafOfModules.smul_freeMk_eq_single r s

/-- The inclusion of the structure presheaf of `O₂` into the base change of the free presheaf of
modules on `F` as the summand indexed by a section `s` of `F`, namely `b ↦ b ⊗ s`. -/
noncomputable def changeOfRingsFreeSingleHom' (X : Cᵒᵖ) (s : F.obj X) :
    (unitPresheaf' O₂).obj X ⟶ (changeOfRingsFreePresheaf' θ F).obj X :=
  letI := (θ.app X).hom.toAlgebra
  AddCommGrpCat.ofHom
    (show (O₂.obj X) →+ TensorProduct (O₁.obj X) (O₂.obj X)
        (((_root_.PresheafOfModules.free (ringPresheaf O₁)).obj F).obj X) from
      { toFun := fun b => b ⊗ₜ[O₁.obj X] (freeGenerator' F X s)
        map_zero' := TensorProduct.zero_tmul _ _
        map_add' := fun a b => TensorProduct.add_tmul a b _ })

/-- `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsFreeSingleHom'` on sections. -/
lemma changeOfRingsFreeSingleHom_apply' (X : Cᵒᵖ) (s : F.obj X) (b : O₂.obj X) :
    letI := (θ.app X).hom.toAlgebra
    changeOfRingsFreeSingleHom' θ F X s b = b ⊗ₜ[O₁.obj X] (freeGenerator' F X s) :=
  rfl

open scoped Classical in
/-- The component of `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsFreeCopowerIso'` at an
object of the site: the base change `O₂(X) ⊗_{O₁(X)} (F(X) →₀ O₁(X))` is `F(X) →₀ O₂(X)`, which
is the copower of `O₂(X)` by `F(X)`. -/
noncomputable def changeOfRingsFreeCopowerIsoApp' (X : Cᵒᵖ) :
    ((unitPresheaf' O₂).copower F).obj X ≅ (changeOfRingsFreePresheaf' θ F).obj X :=
  letI := (θ.app X).hom.toAlgebra
  (AddCommGrpCat.finsuppCopowerIso ((unitPresheaf' O₂).obj X) (F.obj X)).symm ≪≫
    (TensorProduct.finsuppScalarRight (O₁.obj X) (O₂.obj X) (O₂.obj X)
      (F.obj X)).symm.toAddEquiv.toAddCommGrpIso

/-- `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsFreeCopowerIsoApp'` carries the summand
indexed by a section `s` of `F` to the tensors `b ⊗ s`. -/
@[reassoc]
lemma ι_changeOfRingsFreeCopowerIsoApp_hom' (X : Cᵒᵖ) (s : F.obj X) :
    Sigma.ι (fun _ : F.obj X => (unitPresheaf' O₂).obj X) s ≫
        (changeOfRingsFreeCopowerIsoApp' θ F X).hom =
      changeOfRingsFreeSingleHom' θ F X s := by
  classical
  let := (θ.app X).hom.toAlgebra
  have h : Sigma.ι (fun _ : F.obj X => (unitPresheaf' O₂).obj X) s ≫
      (changeOfRingsFreeCopowerIsoApp' θ F X).hom =
        AddCommGrpCat.ofHom (Finsupp.singleAddHom s) ≫
          ((TensorProduct.finsuppScalarRight (O₁.obj X) (O₂.obj X) (O₂.obj X)
            (F.obj X)).symm.toAddEquiv.toAddCommGrpIso).hom := by
    rw [changeOfRingsFreeCopowerIsoApp', Iso.trans_hom, Iso.symm_hom, ← Category.assoc,
      AddCommGrpCat.ι_finsuppCopowerIso_inv]
    rfl
  rw [h]
  ext (b : O₂.obj X)
  exact TensorProduct.finsuppScalarRight_symm_apply_single (R := O₁.obj X) (S := O₂.obj X) s b

/-- **The target half of the copower comparison: the base change of the free presheaf of modules
on a presheaf of sets `F` has underlying presheaf of abelian groups the copower of the structure
presheaf of the target by `F`.** Over each object this is Mathlib's
`TensorProduct.finsuppScalarRight`, `O₂(X) ⊗_{O₁(X)} (F(X) →₀ O₁(X)) = (F(X) →₀ O₂(X))`, and the
restriction maps permute the summands along those of `F`.

`PresheafOfModules.copowerFreeIso'` is the source half, the same statement with no base change. -/
noncomputable def changeOfRingsFreeCopowerIso' :
    (unitPresheaf' O₂).copower F ≅ changeOfRingsFreePresheaf' θ F :=
  NatIso.ofComponents (changeOfRingsFreeCopowerIsoApp' θ F) (by
    intro X Y f
    apply Sigma.hom_ext
    intro s
    rw [Functor.copower_map, Sigma.ι_comp_map'_assoc, ι_changeOfRingsFreeCopowerIsoApp_hom',
      ι_changeOfRingsFreeCopowerIsoApp_hom'_assoc]
    let := (θ.app X).hom.toAlgebra
    let := (θ.app Y).hom.toAlgebra
    ext (b : O₂.obj X)
    change ((O₂.map f).hom b) ⊗ₜ[O₁.obj Y] (freeGenerator' F Y (F.map f s)) =
      (cofMap θ ((_root_.PresheafOfModules.free (ringPresheaf O₁)).obj F) f).hom
        (b ⊗ₜ[O₁.obj X] (freeGenerator' F X s))
    rw [cofMap_tmul]
    congr 1
    exact (freeGenerator_map' F f s).symm)

/-- The components of `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsFreeCopowerIso'`. -/
@[simp]
lemma changeOfRingsFreeCopowerIso_hom_app' (X : Cᵒᵖ) :
    (changeOfRingsFreeCopowerIso' θ F).hom.app X = (changeOfRingsFreeCopowerIsoApp' θ F X).hom :=
  rfl

/-- **The base-change unit at a free presheaf of modules**, read on underlying presheaves of
abelian groups: the component at `R⟨F⟩` of the unit of the change-of-rings adjunction,
`R⟨F⟩ ⟶ O₂ ⊗_{O₁} R⟨F⟩`, which is `m ↦ 1 ⊗ m` on sections. -/
noncomputable def freeUnit' :
    (_root_.PresheafOfModules.toPresheaf (ringPresheaf O₁)).obj
        ((_root_.PresheafOfModules.free (ringPresheaf O₁)).obj F) ⟶
      changeOfRingsFreePresheaf' θ F :=
  (Functor.whiskerRight (changeOfRingsAdjunction θ).unit
    (_root_.PresheafOfModules.toPresheaf (ringPresheaf O₁))).app
      ((_root_.PresheafOfModules.free (ringPresheaf O₁)).obj F)

/-- `Stacks.PresheafOfModules.ChangeOfRings.freeUnit'` is `m ↦ 1 ⊗ m` on sections. -/
lemma freeUnit_app_apply' (X : Cᵒᵖ)
    (m : ((_root_.PresheafOfModules.free (ringPresheaf O₁)).obj F).obj X) :
    letI := (θ.app X).hom.toAlgebra
    (freeUnit' θ F).app X m = (1 : O₂.obj X) ⊗ₜ[O₁.obj X] m :=
  changeOfRingsAdjunction_unit_app_apply θ _ X m

/-- **On sections the base-change unit at a free presheaf of modules sends the function supported
at a section `s` of `F` with value `r` to `θ(r) ⊗ s`.** -/
lemma freeUnit_app_single' (X : Cᵒᵖ) (s : F.obj X) (r : O₁.obj X) :
    letI := (θ.app X).hom.toAlgebra
    (freeUnit' θ F).app X (Finsupp.single s r) =
      ((θ.app X).hom r) ⊗ₜ[O₁.obj X] (freeGenerator' F X s) := by
  let := (θ.app X).hom.toAlgebra
  have h1 : (1 : O₂.obj X) ⊗ₜ[O₁.obj X]
        (r • freeGenerator' (R := ringPresheaf O₁) F X s) =
      ((θ.app X).hom r) ⊗ₜ[O₁.obj X] (freeGenerator' (R := ringPresheaf O₁) F X s) := by
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    change r • (1 : O₂.obj X) = (θ.app X).hom r
    rw [Algebra.smul_def, mul_one]
    rfl
  refine Eq.trans (freeUnit_app_apply' θ F X (Finsupp.single s r)) (Eq.trans ?_ h1)
  exact congrArg (fun m : ((_root_.PresheafOfModules.free (ringPresheaf O₁)).obj F).obj X =>
    (1 : O₂.obj X) ⊗ₜ[O₁.obj X] m) (smul_freeGenerator' (R := ringPresheaf O₁) F X s r).symm

/-- **The square identifying the base-change unit at a free presheaf of modules with the copower
of the augmentation.** Under `PresheafOfModules.copowerFreeIso'` and
`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsFreeCopowerIso'`, the unit
`R⟨F⟩ ⟶ O₂ ⊗_{O₁} R⟨F⟩` of the change-of-rings adjunction at a free presheaf of modules is the
copower by `F` of the map of structure presheaves underlying `θ`. On sections, on the summand
indexed by a section `s` of `F`, both sides send `r` to `θ(r) ⊗ s`. -/
lemma copowerFreeIso_unitMap_copowerMap' :
    Functor.copowerMap (unitMap' θ) (𝟙 F) ≫ (changeOfRingsFreeCopowerIso' θ F).hom =
      (_root_.PresheafOfModules.copowerFreeIso' (ringPresheaf O₁) F).hom ≫ freeUnit' θ F := by
  apply NatTrans.ext
  funext X
  apply Sigma.hom_ext
  intro s
  let := (θ.app X).hom.toAlgebra
  ext r
  have hL : (Functor.copowerMap (unitMap' θ) (𝟙 F)).app X
        (Sigma.ι (fun _ : F.obj X => (unitPresheaf' O₁).obj X) s r) =
      Sigma.ι (fun _ : F.obj X => (unitPresheaf' O₂).obj X) s ((unitMap' θ).app X r) :=
    apply_comp_of_comp_eq (Functor.ι_copowerMap_app (unitMap' θ) (𝟙 F) X s) r
  have hR : (_root_.PresheafOfModules.copowerFreeIso' (ringPresheaf O₁) F).hom.app X
        (Sigma.ι (fun _ : F.obj X => (unitPresheaf' O₁).obj X) s r) =
      Finsupp.single s r :=
    apply_comp_of_comp_eq
      (_root_.PresheafOfModules.ι_copowerFreeIsoApp_hom' (ringPresheaf O₁) F X s) r
  have hι : (changeOfRingsFreeCopowerIso' θ F).hom.app X
        (Sigma.ι (fun _ : F.obj X => (unitPresheaf' O₂).obj X) s ((unitMap' θ).app X r)) =
      ((θ.app X).hom r) ⊗ₜ[O₁.obj X] (freeGenerator' F X s) :=
    apply_comp_of_comp_eq (ι_changeOfRingsFreeCopowerIsoApp_hom' θ F X s) _
  simp only [NatTrans.comp_app, CategoryTheory.comp_apply]
  rw [hL, hι, hR]
  exact (freeUnit_app_single' θ F X s r).symm

end Stacks.PresheafOfModules.ChangeOfRings

/-! ### The column step for an arbitrary homomorphism of simplicial rings

Tag 08RX is stated for an arbitrary map `O ⟶ O'` of sheaves of rings; read at `C = Δ` that is an
arbitrary homomorphism `φ : O ⟶ O'` of simplicial commutative rings, not only an augmentation
to a constant simplicial ring. The declarations carry the names of their counterparts for an
augmentation with a prime. -/

namespace Stacks.SimplicialModules

open Stacks.PresheafOfModules.ChangeOfRings

variable {O O' : SimplexCategoryᵒᵖ ⥤ CommRingCat.{u}} (φ : O ⟶ O')

/-- **The base-change unit read on Moore complexes**, `s(Q_•) ⟶ s(Q_• ⊗_{O_•} O'_•)`: the unit of
the change-of-rings adjunction `Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsAdjunction`
along the augmentation `φ`, whiskered onto underlying presheaves of abelian groups and then onto
Moore complexes.

The Δ-instance of [Stacks, Tag 08RX] asserts that this is a quasi-isomorphism at every
degreewise flat simplicial `O`-module as soon as it is one at
`PresheafOfModules.unit (ringPresheaf O)`, which is the statement `O ⊗_O O' = O'`; see the
implementation notes of this module for what is proved towards it. -/
def mooreCochainBaseChange' :
    mooreCochain O ⟶ changeOfRings φ ⋙ mooreCochain O' :=
  Functor.whiskerRight
    (Functor.whiskerRight (changeOfRingsAdjunction φ).unit
      (PresheafOfModules.toPresheaf (ringPresheaf O)))
    (alternatingFaceMapCochainComplex AddCommGrpCat.{u})

/-- Degreewise, base change along `φ` is Mathlib's extension of scalars. This holds by
definition, and is what lets the row direction of the intended proof consume flatness through
`CochainComplex.DerivedTensor.KFlatDerived.quasiIso_extendScalars_map_of_kFlat`. -/
lemma changeOfRings_obj_obj' (M : SMod O) (n : SimplexCategoryᵒᵖ) :
    ((changeOfRings φ).obj M).obj n =
      (ModuleCat.extendScalars (R := O.obj n) (S := O'.obj n) (φ.app n).hom).obj (M.obj n) :=
  rfl

/-- **The base-change unit is a quasi-isomorphism at a free simplicial module on a contractible
simplicial set**, as soon as it is one on the underlying simplicial abelian groups of the
homomorphism of structure rings itself. This is the column step of the Δ-instance of
[Stacks, Tag 08RX]: the
underlying simplicial abelian group of `O⟨F⟩` is the product of `F` with `O_•`
(`PresheafOfModules.copowerFreeIso'`), that of its base change is the product of `F` with `O'`
(`Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsFreeCopowerIso'`), the unit is the product of
`F` with the homomorphism of structure rings
(`Stacks.PresheafOfModules.ChangeOfRings.copowerFreeIso_unitMap_copowerMap'`), and multiplying by a
contractible simplicial set does not change which maps the homology of the Moore complex inverts
(`AlgebraicTopology.quasiIso_alternatingFaceMapCochainComplex_map_copowerMap`).

Here `F` is given together with a homotopy equivalence `a : F ⟶ ∗` onto the constant simplicial
set on a singleton; at `F = Δ[m]` such an `a` is
`SSet.stdSimplex.homotopyEquivalences_hom_obj₀`. -/
theorem quasiIso_mooreCochainBaseChange_app_free' {F : SimplexCategoryᵒᵖ ⥤ Type u}
    {a : F ⟶ (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{u + 1}}
    (ha : SimplicialObject.homotopyEquivalences (Type u) a)
    (hφ : QuasiIso ((alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map (unitMap' φ))) :
    QuasiIso ((mooreCochainBaseChange' φ).app
      ((PresheafOfModules.free (ringPresheaf O)).obj F)) := by
  have hcop : QuasiIso ((alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map
      (Functor.copowerMap (unitMap' φ) (𝟙 F))) :=
    quasiIso_alternatingFaceMapCochainComplex_map_copowerMap _ ha hφ
  have key : (mooreCochainBaseChange' φ).app ((PresheafOfModules.free (ringPresheaf O)).obj F) =
      (alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map
        ((PresheafOfModules.copowerFreeIso' (ringPresheaf O) F).inv ≫
          Functor.copowerMap (unitMap' φ) (𝟙 F) ≫ (changeOfRingsFreeCopowerIso' φ F).hom) := by
    rw [copowerFreeIso_unitMap_copowerMap', ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rfl
  rw [key, Functor.map_comp, Functor.map_comp]
  infer_instance


/-- **The base-change unit is a quasi-isomorphism at the free simplicial module on a standard
simplex**, the standard simplices being contractible ([Stacks, Tag 08QD]). -/
theorem quasiIso_mooreCochainBaseChange_app_freeStdSimplex' (m : SimplexCategory)
    (hφ : QuasiIso ((alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map (unitMap' φ))) :
    QuasiIso ((mooreCochainBaseChange' φ).app
      ((PresheafOfModules.free (ringPresheaf O)).obj ((SSet.stdSimplex.{u}).obj m))) :=
  quasiIso_mooreCochainBaseChange_app_free' φ
    (SimplicialObject.homotopyEquivalences_iso_comp_iso (Iso.refl _)
      ((SSet.stdSimplex.{u}).map (default : m ⟶ SimplexCategory.mk 0)) stdSimplexZeroIsoConst
      ((SSet.stdSimplex.homotopyEquivalences_hom_obj₀ m.len).1 _)) hφ

/-- **The column step of the Δ-instance of [Stacks, Tag 08RX]: the base-change unit is a
quasi-isomorphism at the canonical cover of any simplicial module by free simplicial modules on
standard simplices.** The cover is a coproduct, indexed by the sections of `M`, of free
simplicial modules on standard simplices (`PresheafOfModules.stdCover'`); the base-change unit is
a quasi-isomorphism at each summand by
`Stacks.SimplicialModules.quasiIso_mooreCochainBaseChange_app_freeStdSimplex'`, both sides take
coproducts to coproducts, and a coproduct of quasi-isomorphisms of cochain complexes of abelian
groups is a quasi-isomorphism (`CochainComplex.quasiIso_sigmaMap`, Grothendieck's AB4). -/
theorem quasiIso_mooreCochainBaseChange_app_stdCover' (M : SMod O)
    (hφ : QuasiIso ((alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map (unitMap' φ))) :
    QuasiIso ((mooreCochainBaseChange' φ).app M.stdCover') :=
  CochainComplex.quasiIso_app_sigma (mooreCochainBaseChange' φ) _
    (fun m => quasiIso_mooreCochainBaseChange_app_freeStdSimplex' φ m.1.unop hφ)

end Stacks.SimplicialModules

end
