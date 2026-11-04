module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolutionAbelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitCoefficientTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekFreeModuleBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.FlatBaseChangeOfSimplicialModules
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteCotangentComplex
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteSmall
public import StacksFrontier.Cotangent.ResolutionPointCriterionSmall
import all StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.EvaluationToDerivedColimit
import all StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedChangeOfCoefficients
import all StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitCoefficientTensor
import StacksCore.Tactic.StacksAttribute

/-!
# The structure presheaf of rings on the small model of `C_{B/A}`, and its augmentation

Let `A → B` be a ring map and let `κ` be a cardinal. The small model
`CommAlgCat.smallBoundedPolynomialSite A B κ` of the site `C_{B/A}` of [Stacks, Tag 08PR] is a
`SmallCategory` in `Type u`, and this file equips it with the two presheaves of rings between
which the change of coefficients of [Stacks, Tag 08QJ] takes place:

* the tautological presheaf `𝒪`, sending an object `(P, α)` to the ring `P`;
* the constant presheaf `B̲` with value `B`;

together with the map `𝒪 ⟶ B̲` given by the augmentations.

Both have their sections in `Type u`, which is what distinguishes them from
`CommAlgCat.polynomialStructurePresheaf` and `CommAlgCat.polynomialConstantPresheaf`: those are
formed on the unrestricted site and have their sections lifted to `Type (u + 1)`, the universe in
which the morphism of topoi `π` of [Stacks, Tag 08PR] is built. The derived lower shriek of
[Stacks, Tag 08Q6] takes coefficients in `AddCommGrpCat.{u}` for a site in `Type u`, and the
change-of-coefficients API
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitCoefficientTensor` takes a
morphism of presheaves of rings valued in `RingCat.{u}`; neither can be fed the universe-lifted
sections of the unrestricted site. Hence the small model, and hence `RingCat.{u}`.

## Main definitions

* `CommAlgCat.overRingFunctor` and `CommAlgCat.overStructureAugmentation`: an object of `Over B` in
  `CommAlgCat A`, read as a ring, and its augmentation to `B`.
* `CommAlgCat.smallPolynomialStructurePresheaf`: the tautological presheaf of rings `𝒪` on the
  small model, with sections in `Type u`.
* `CommAlgCat.smallPolynomialConstantPresheaf`: the constant presheaf `B̲`.
* `CommAlgCat.smallPolynomialAugmentation`: the map `𝒪 ⟶ B̲`.
* `CommAlgCat.polynomialStructurePresheafRing` and `CommAlgCat.polynomialAugmentationRing`: the
  same two constructions on the unrestricted site `CommAlgCat.polynomialSite`, again with
  sections in `Type u`.
* `CommAlgCat.smallPolynomialAugmentationAbelian`: the map `𝒪 ⟶ B̲` read on the underlying
  abelian presheaves, which is the shape in which [Stacks, Tag 08RX] asks for it.
* `CommAlgCat.smallResolutionStructureRingIso`: the comparison `𝒪(P_•, ε) ≅ P_•` identifying the
  evaluation of `𝒪` on the cosimplicial object of a bounded resolution, read in the small model,
  with the simplicial ring underlying that resolution.
* `Stacks.ChaoticSite.freeCopowerIso`: **`j_{W!}R_W` as a copower** — the abelian presheaf
  underlying the free presheaf of modules `R⟨F⟩` on a presheaf of sets `F` is the copower
  `V ↦ ⊕_{s ∈ F(V)} R(V)` of `R` by `F`, for a site whose objects *and morphisms* live in the
  universe of the rings. This is the universe-general form of
  `PresheafOfModules.copowerFreeIso`.
* `Stacks.ChaoticSite.freeExtendScalarsUnit`: the canonical map `R⟨F⟩ ⟶ R'⟨F⟩` of `R`-modules
  made out of the unit of the change-of-coefficients adjunction and
  `Stacks.ChaoticSite.freeCompExtendScalarsIso`, which is `R⟨F⟩ ⊗_R R' = R'⟨F⟩`.
* `Stacks.ChaoticSite.mooreCochainUnit`: the change-of-coefficients unit
  `ℱ ⟶ ℱ ⊗_𝒪 𝒪'` read on the extended Moore complexes of the evaluation on a cosimplicial
  object, as a natural transformation of functors of the `𝒪`-module.

## Main results

* `CommAlgCat.smallPolynomialStructurePresheaf_eq` and
  `CommAlgCat.smallPolynomialAugmentation_eq`: the constructions on the small model are the
  restrictions of those on the unrestricted site, on the nose.
* `CommAlgCat.polynomialStructurePresheafRing_comp_resolution` and
  `CommAlgCat.polynomialAugmentationRing_comp_resolution`: **evaluating `𝒪` and `𝒪 ⟶ B̲` on the
  cosimplicial object of a resolution `ε : P_• ⟶ B` returns the simplicial ring `P_•` and the
  augmentation `ε` itself**, on the nose. These are the identifications that let the criterion of
  [Stacks, Tag 08QI] be read as a statement about the Moore complex of the evaluation of `𝒪` on a
  point resolution, which is the form in which the second hypothesis of [Stacks, Tag 08RX] is
  stated.
* `CommAlgCat.smallPolynomialAugmentation_comp_resolution`: the same identification on the small
  model, where it is no longer an equality but a transport along
  `CommAlgCat.smallResolutionStructureRingIso`.
* `CommAlgCat.quasiIso_mooreCochainComplex_map_smallPolynomialAugmentation` and
  `CommAlgCat.isIso_totalDerivedColimit_smallPolynomialAugmentation`: **`Lπ_!(𝒪) = Lπ_!(B̲)`**,
  first as a quasi-isomorphism of Moore complexes and then as an isomorphism in `D(Ab)`. This is
  the second hypothesis of [Stacks, Tag 08RX]; the first is
  `CommAlgCat.isPointResolution_standardResolutionSmallCosimplicialObject`.
* `CommAlgCat.isIso_leftDerivedColimit_map_smallPolynomialAugmentationAbelian`: the same
  statement read degreewise, `L_nπ_!(𝒪) = L_nπ_!(B̲)` for every `n`.
* `CommAlgCat.isIso_leftDerivedColimit_map_extensionByZero_smallPolynomialAugmentation`: **the
  generator step of [Stacks, Tag 08RX] for `𝒪 ⟶ B̲`, unconditionally** — `L_nπ_!` also inverts
  `j_{W!}𝒪_W ⟶ j_{W!}B̲_W` for every object `W` of the model.
* `Stacks.ChaoticSite.freeCopowerIso_hom_comp_map_freeExtendScalarsUnit`: **the
  change-of-coefficients unit at a free presheaf of modules is the copower of the coefficient
  map**, under the two copower identifications.
* `Stacks.ChaoticSite.quasiIso_mooreCochainComplex_map_iff`: a morphism of abelian presheaves is a
  quasi-isomorphism on the extended Moore complexes of its evaluation on a cosimplicial object
  exactly when the homology of the Moore complex inverts it in every degree. This is the
  translation between the two forms of [Stacks, Tag 08Q9] used here.
* `Stacks.ChaoticSite.quasiIso_mooreCochainComplex_map_unit_free` and
  `CommAlgCat.quasiIso_mooreCochainComplex_map_unit_free_smallPolynomialAugmentation`: **the
  column step of [Stacks, Tag 08RX] at the generators**, in general and then for `𝒪 ⟶ B̲` with
  every hypothesis discharged — the unit `j_{W!}𝒪_W ⟶ j_{W!}𝒪_W ⊗_𝒪 B̲` is a quasi-isomorphism on
  the extended Moore complex of its evaluation on the standard resolution.
* `Stacks.ChaoticSite.quasiIso_mooreCochainUnit_app_sigma`,
  `Stacks.ChaoticSite.quasiIso_mooreCochainUnit_app_freeYonedaCoproduct` and
  `Stacks.ChaoticSite.quasiIso_mooreCochainUnit_app_of_projective`: **the dévissage of
  [Stacks, Tag 08RX] from the generators to an arbitrary projective presheaf of modules** — the
  unit is a quasi-isomorphism on extended Moore complexes at a coproduct as soon as it is one at
  every summand, hence at the canonical cover of a module by free modules on representables,
  hence at every projective module, a projective module being a retract of that cover.
* `Stacks.ChaoticSite.AbelianValued.isIso_totalDerivedColimit_map_of_quasiIso_columns`:
  **derived lower shriek inverts a morphism of bounded above complexes of abelian presheaves
  which is a quasi-isomorphism on extended Moore complexes in every degree.** This is
  [Stacks, Tag 0133] for the Moore double complex, with the hypothesis on the columns.
* `Stacks.ChaoticSite.isIso_map_derivedExtendScalarsAdjunction_unit_app_Q_iff`: **at a
  K-projective complex the unit of the derived change-of-coefficients adjunction is inverted by
  a functor exactly when the degreewise underived unit is.**
* `Stacks.ChaoticSite.isIso_derivedColimitTensorComparison_app_single`: **[Stacks, Tag 08QJ] on
  an arbitrary chaotic site** — for a point resolution and a coefficient map inverted by `L_nπ_!`
  in every degree, `Lπ_!(ℱ) ⟶ Lπ_!(ℱ ⊗^L_𝒪 𝒪')` is invertible for every `𝒪`-module `ℱ` in
  degree zero.
* `CommAlgCat.isIso_derivedColimitTensorComparison_smallPolynomialAugmentation`:
  **[Stacks, Tag 08QJ]** — `Lπ_!(ℱ) = Lπ_!(ℱ ⊗^L_𝒪 B̲)` for an `𝒪`-module `ℱ` on the small model
  of `C_{B/A}`, with every hypothesis discharged.

## Implementation notes

The three constructions on the site are obtained by restricting constructions on `Over B` along
`CommAlgCat.smallSiteToOver`, so that the naturality of the augmentation is exactly the
commutativity `CategoryTheory.Over.w` of a morphism over `B` and no computation on the site is
performed.

All four identifications hold by `rfl`. This is the same phenomenon as in
`CommAlgCat.standardResolutionOverDifferentialsIso`, which identifies the evaluation of
`i^*Ω_{𝒪/A}` on the standard resolution with the cotangent simplicial module and is likewise
componentwise the identity: the inclusions of the small model and of the restricted site into the
unrestricted one, and the passage from a resolution to its cosimplicial object, are all built
from `CategoryTheory.ObjectProperty.ι`, `CategoryTheory.Functor.rightOp` and
`CategoryTheory.unopUnop`, none of which does anything to the underlying object of `Over B`.

**Where an isomorphism becomes unavoidable.** Passing from the unrestricted site to the *small
model* does not: `CommAlgCat.smallResolutionCosimplicialObject` is the cosimplicial object of a
bounded resolution composed with the inverse of the equivalence
`CommAlgCat.boundedPolynomialSiteEquiv`, so its objects are only isomorphic to the terms of the
resolution. Hence `CommAlgCat.smallResolutionStructureRingIso` is a comparison isomorphism and
`CommAlgCat.smallPolynomialAugmentation_comp_resolution` a transport along it, rather than two
more `rfl`s. On the target of the augmentation nothing has to be transported: `B̲` is constant, so
both readings of `B̲(P_•, ε)` are the constant simplicial ring on `B` on the nose, and the
comparison of augmented simplicial rings is a triangle rather than a square.

**How [Stacks, Tag 08QJ] is proved here.** The change of coefficients of [Stacks, Tag 08QJ] is
the assertion that `Lπ_!(ℱ) ⟶ Lπ_!(ℱ ⊗^L_𝒪 B̲)` is invertible for an `𝒪`-module `ℱ`. The source
writes the right-hand side as `Lπ_!(Li^*ℱ)`; on a chaotic site the morphism of topoi `i` is the
identity on topoi, so `Li^*ℱ` and `ℱ ⊗^L_𝒪 B̲` are one and the same object of `D(Mod(B̲))` and
the two readings of the statement coincide. The comparison itself is
`Stacks.ChaoticSite.derivedColimitTensorComparison`, and its invertibility at an `𝒪`-module in
cohomological degree zero is
`CommAlgCat.isIso_derivedColimitTensorComparison_smallPolynomialAugmentation`.

The dévissage of [Stacks, Tag 08RX] is carried out on **Moore double complexes** rather than on
homotopy colimits in `D(Mod(𝒪))`, which is what keeps it elementary: it needs no
`CategoryTheory.NatTrans.CommShift` structure on the comparison, no homotopy colimit and no
coproduct in `D(Mod(𝒪))`. Starting from the generator step
`CommAlgCat.quasiIso_mooreCochainComplex_map_unit_free_smallPolynomialAugmentation`, the four
remaining steps are: the passage from a generator to a coproduct of generators
(`Stacks.ChaoticSite.quasiIso_mooreCochainUnit_app_sigma`, which is Grothendieck's axiom AB4 for
quasi-isomorphisms, `CochainComplex.quasiIso_app_sigma`); the passage from a coproduct of
generators to an arbitrary projective module, which is a retract of the canonical such coproduct
(`Stacks.ChaoticSite.quasiIso_mooreCochainUnit_app_of_projective`); the comparison of the two
filtrations of the Moore double complex of a bounded above complex, which turns a degreewise
quasi-isomorphism of Moore complexes into an isomorphism after `Lπ_!`
(`Stacks.ChaoticSite.AbelianValued.isIso_totalDerivedColimit_map_of_quasiIso_columns`);
and the identification of the *derived* change-of-coefficients unit at a K-projective complex
with the degreewise underived one
(`Stacks.ChaoticSite.isIso_map_derivedExtendScalarsAdjunction_unit_app_Q_iff`, from
`CategoryTheory.Adjunction.derivedη_fac_app` and
`Stacks.Homology.isIso_leftDerivedCounit_app_of_isKProjective`). An `𝒪`-module placed in degree
zero is then resolved by a bounded above complex of projective presheaves of modules
([Stacks, Tag 0646]) and the four steps compose.

**Why three modules are imported twice.** The derived tensor product, its adjunction and the
comparison `Stacks.ChaoticSite.derivedColimitTensorComparison` are definitions whose bodies the
modules that state them do not export, so the components of the comparison cannot be computed
from the public interface alone; the extra `import all` directives make those bodies available.
They are used for exactly two definitional unfoldings: that the comparison is `Lπ_!` of the
derived unit followed by `Stacks.ChaoticSite.restrictScalarsDerivedColimitIso`
(`Stacks.ChaoticSite.isIso_derivedColimitTensorComparison_app_iff`), and that the unit of the
derived change-of-coefficients adjunction is the `CategoryTheory.Adjunction.derivedη` of the
underived one
(`Stacks.ChaoticSite.isIso_map_derivedExtendScalarsAdjunction_unit_app_Qh_iff`).

**Why the copower identification is restated here.** The identification of the abelian presheaf
underlying a free presheaf of modules with a copower of the structure presheaf already exists as
`PresheafOfModules.copowerFreeIso`, but only for a site whose objects and morphisms both form
types in `Type 0`; the parallel identification of the change-of-coefficients unit,
`Stacks.PresheafOfModules.ChangeOfRings.copowerFreeIso_unitMap_copowerMap`, is moreover stated for
presheaves of *commutative* rings and for the explicit tensor-product construction of base change.
The small model of `C_{B/A}` has its morphisms in `Type u` together with its rings, and the
change-of-coefficients functor used here is the abstract left adjoint of restriction of scalars, so
neither applies. Both are therefore restated in the generality needed. The unit is pinned down
without any computation with tensor products: by uniqueness of left adjoints it fixes the
tautological generators (`Stacks.ChaoticSite.freeExtendScalarsUnit_freeMk`), which determines it on
sections by `𝒪`-linearity.

## References

* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 0646](https://stacks.math.columbia.edu/tag/0646)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08PS](https://stacks.math.columbia.edu/tag/08PS)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
* [Stacks Project, Tag 08QJ](https://stacks.math.columbia.edu/tag/08QJ)
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

/-! ### The free presheaf of modules as a copower, at a site whose homs are in `Type u` -/

namespace Stacks.ChaoticSite

universe u

section FreeCopower

variable {C : Type u} [SmallCategory C] (R : Cᵒᵖ ⥤ RingCat.{u}) (F : Cᵒᵖ ⥤ Type u)

/-- **The presheaf of abelian groups underlying a presheaf of rings**, `𝒪` read additively. It is
also the presheaf underlying the structure presheaf of modules `PresheafOfModules.unit R`, on the
nose. -/
abbrev ringAbelianPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  R ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}

/-- The inclusion of `R` into the free presheaf of modules on a presheaf of sets `F` as the
summand indexed by a section `s` of `F` over an object of the site, read on underlying abelian
groups: it sends `r` to the function supported at `s` with value `r`. -/
def freeSummandι (X : Cᵒᵖ) (s : F.obj X) :
    (ringAbelianPresheaf R).obj X ⟶
      ((PresheafOfModules.toPresheaf R).obj ((PresheafOfModules.free R).obj F)).obj X :=
  AddCommGrpCat.ofHom (Finsupp.singleAddHom s)

/-- The component of `Stacks.ChaoticSite.freeCopowerIso` at an object of the site: over `X` the
free module on `F(X)` is the direct sum of `F(X)`-many copies of `R(X)`. -/
def freeCopowerIsoApp (X : Cᵒᵖ) :
    ((ringAbelianPresheaf R).copower F).obj X ≅
      ((PresheafOfModules.toPresheaf R).obj ((PresheafOfModules.free R).obj F)).obj X :=
  (AddCommGrpCat.finsuppCopowerIso ((ringAbelianPresheaf R).obj X) (F.obj X)).symm

/-- `Stacks.ChaoticSite.freeCopowerIsoApp` carries the summand indexed by a section `s` of `F` to
the functions supported at `s`. -/
@[reassoc]
lemma ι_freeCopowerIsoApp_hom (X : Cᵒᵖ) (s : F.obj X) :
    Sigma.ι (fun _ : F.obj X => (ringAbelianPresheaf R).obj X) s ≫
      (freeCopowerIsoApp R F X).hom = freeSummandι R F X s :=
  AddCommGrpCat.ι_finsuppCopowerIso_inv _ _ s

/-- The summand inclusions of `Stacks.ChaoticSite.freeSummandι` are compatible with the
restriction maps: restricting and then including at the restricted index agrees with including
and then restricting. -/
lemma freeSummandι_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) (s : F.obj X) :
    (ringAbelianPresheaf R).map f ≫ freeSummandι R F Y (F.map f s) =
      freeSummandι R F X s ≫
        ((PresheafOfModules.toPresheaf R).obj ((PresheafOfModules.free R).obj F)).map f := by
  ext (r : R.obj X)
  show Finsupp.single ((F.map f) s) ((R.map f) r) =
    ((PresheafOfModules.free R).obj F).map f (Finsupp.single s r)
  have h1 : (Finsupp.single s r : ((PresheafOfModules.free R).obj F).obj X) =
      r • ModuleCat.freeMk (R := R.obj X) s := by
    show (Finsupp.single s r : F.obj X →₀ R.obj X) = r • Finsupp.single s (1 : R.obj X)
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  have h2 : ((PresheafOfModules.free R).obj F).map f (ModuleCat.freeMk (R := R.obj X) s) =
      ModuleCat.freeMk (R := R.obj Y) ((F.map f) s) := ModuleCat.freeDesc_apply _ _
  have h3 := PresheafOfModules.map_smul ((PresheafOfModules.free R).obj F) f r
    (ModuleCat.freeMk (R := R.obj X) s)
  rw [h2] at h3
  have h4 : (R.map f) r • ModuleCat.freeMk (R := R.obj Y) ((F.map f) s) =
      Finsupp.single ((F.map f) s) ((R.map f) r) := by
    show (R.map f) r • Finsupp.single ((F.map f) s) (1 : R.obj Y) = _
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [h1]
  exact (h3.trans h4).symm

/-- **The abelian presheaf underlying the free presheaf of modules `R⟨F⟩` on a presheaf of sets
`F` is the copower of `R` by `F`**, i.e. `V ↦ ⊕_{s ∈ F(V)} R(V)`. Over each object the free module
on `F(X)` is the direct sum of `F(X)`-many copies of `R(X)`, and the restriction maps of the free
presheaf of modules permute the summands along those of `F`.

This is `PresheafOfModules.copowerFreeIso` with the universe restriction removed: that version is
stated for a site whose objects *and morphisms* form types in `Type 0`, which rules out the small
model of `C_{B/A}`, whose morphisms live in `Type u` together with its rings. Nothing else
changes; `PresheafOfModules.free` itself is stated for an arbitrary site and a presheaf of rings
in `RingCat.{u}`. At `F` the presheaf represented by an object `W` this is the extension by zero
`j_{W!}R_W` of [Stacks, Tag 08RX], in the copower form in which
`Stacks.ChaoticSite.extensionByZeroPresheaf` records it. -/
def freeCopowerIso :
    (ringAbelianPresheaf R).copower F ≅
      (PresheafOfModules.toPresheaf R).obj ((PresheafOfModules.free R).obj F) :=
  NatIso.ofComponents (freeCopowerIsoApp R F) (by
    intro X Y f
    apply Sigma.hom_ext
    intro s
    rw [Functor.copower_map, Sigma.ι_comp_map'_assoc, ι_freeCopowerIsoApp_hom, ← Category.assoc,
      ι_freeCopowerIsoApp_hom]
    exact freeSummandι_naturality R F f s)

/-- The components of `Stacks.ChaoticSite.freeCopowerIso`. -/
@[simp]
lemma freeCopowerIso_hom_app (X : Cᵒᵖ) :
    (freeCopowerIso R F).hom.app X = (freeCopowerIsoApp R F X).hom :=
  rfl

end FreeCopower

/-! ### The change-of-coefficients unit at a free presheaf of modules -/

section FreeExtendScalars

variable {C : Type u} [SmallCategory C] {O O' : Cᵒᵖ ⥤ RingCat.{u}} (a : O ⟶ O')

/-- **The canonical map `O⟨F⟩ ⟶ O'⟨F⟩` of `O`-modules**: the unit of the change-of-rings
adjunction at the free `O`-module on `F`, followed by the identification
`Stacks.ChaoticSite.freeCompExtendScalarsIso` of its target with the free `O'`-module on `F`. The
second factor is invertible, so this map and the unit itself are inverted by the same
functors. -/
def freeExtendScalarsUnit (F : Cᵒᵖ ⥤ Type u) :
    (PresheafOfModules.free.{u} O).obj F ⟶
      (PresheafOfModules.restrictScalars.{u} a).obj ((PresheafOfModules.free.{u} O').obj F) :=
  (changeOfRingsAdjunction a).unit.app ((PresheafOfModules.free.{u} O).obj F) ≫
    (PresheafOfModules.restrictScalars.{u} a).map ((freeCompExtendScalarsIso a).hom.app F)

/-- **`Stacks.ChaoticSite.freeExtendScalarsUnit` fixes the tautological generators**: it carries
the generator of `O⟨F⟩` attached to a section `s` of `F` to the generator of `O'⟨F⟩` attached to
the same section. This is the defining property of
`CategoryTheory.Adjunction.leftAdjointUniq`, read through the free-module adjunction:
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app` says exactly that the two units
agree after transport, and the unit of the free-module adjunction is `s ↦ ModuleCat.freeMk s`. -/
lemma freeExtendScalarsUnit_freeMk (F : Cᵒᵖ ⥤ Type u) (X : Cᵒᵖ) (s : F.obj X) :
    (freeExtendScalarsUnit a F).app X (ModuleCat.freeMk s) =
      ModuleCat.freeMk (R := O'.obj X) s := by
  have key := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((PresheafOfModules.freeAdjunction.{u} O).comp (changeOfRingsAdjunction a))
    (PresheafOfModules.freeAdjunction.{u} O') F
  rw [Adjunction.comp_homEquiv, Equiv.trans_apply,
    PresheafOfModules.freeAdjunction_homEquiv] at key
  have h2 := congrArg (fun φ : F ⟶ _ => φ.app X s) key
  simp only [PresheafOfModules.freeHomEquiv,
    PresheafOfModules.freeAdjunctionUnit_app,
    PresheafOfModules.freeAdjunction_unit_app] at h2
  exact h2

/-- **`Stacks.ChaoticSite.freeExtendScalarsUnit` on sections**: it sends the function supported at
a section `s` of `F` with value `r` to the function supported at `s` with value `a(r)`. The map is
`O`-linear and `Finsupp.single s r = r • ModuleCat.freeMk s`, so this follows from
`Stacks.ChaoticSite.freeExtendScalarsUnit_freeMk` and the fact that the `O`-action on the
restriction of scalars of an `O'`-module is the `O'`-action along `a`. -/
lemma freeExtendScalarsUnit_single (F : Cᵒᵖ ⥤ Type u) (X : Cᵒᵖ) (s : F.obj X) (r : O.obj X) :
    (freeExtendScalarsUnit a F).app X (Finsupp.single s r) =
      Finsupp.single s ((a.app X).hom r) := by
  have h1 : (Finsupp.single s r : ((PresheafOfModules.free.{u} O).obj F).obj X) =
      r • ModuleCat.freeMk (R := O.obj X) s := by
    show (Finsupp.single s r : F.obj X →₀ O.obj X) = r • Finsupp.single s (1 : O.obj X)
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  have hsm : (freeExtendScalarsUnit a F).app X
        (r • (ModuleCat.freeMk s : ((PresheafOfModules.free.{u} O).obj F).obj X)) =
      r • (freeExtendScalarsUnit a F).app X
        (ModuleCat.freeMk s : ((PresheafOfModules.free.{u} O).obj F).obj X) :=
    map_smul _ r _
  rw [h1, hsm, freeExtendScalarsUnit_freeMk]
  show (a.app X).hom r • Finsupp.single s (1 : O'.obj X) = _
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- **The change-of-coefficients unit at a free presheaf of modules is the copower of the
coefficient map.** Under the two identifications
`Stacks.ChaoticSite.freeCopowerIso` of the abelian presheaves underlying `O⟨F⟩` and `O'⟨F⟩` with
the copowers of `O` and `O'` by `F`, the canonical map
`Stacks.ChaoticSite.freeExtendScalarsUnit` is the copower by `F` of the map of abelian presheaves
underlying `a`. On the summand indexed by a section `s` of `F` both sides send `r` to the function
supported at `s` with value `a(r)`.

This is the identification that lets the generator step of [Stacks, Tag 08RX] be read off from the
hypothesis on the coefficient map alone, the generators `j_{W!}O_W` of that proof being the free
modules on the representable presheaves. The factor
`PresheafOfModules.restrictScalarsCompToPresheaf` is the identity; it is spelled out only so that
both sides of the equation are typed by the same functor. -/
lemma freeCopowerIso_hom_comp_map_freeExtendScalarsUnit (F : Cᵒᵖ ⥤ Type u) :
    (freeCopowerIso O F).hom ≫
        (PresheafOfModules.toPresheaf O).map (freeExtendScalarsUnit a F) ≫
          (PresheafOfModules.restrictScalarsCompToPresheaf.{u} a).hom.app
            ((PresheafOfModules.free.{u} O').obj F) =
      Functor.copowerMap (Functor.whiskerRight a (forget₂ RingCat.{u} AddCommGrpCat.{u}))
          (𝟙 F) ≫ (freeCopowerIso O' F).hom := by
  apply NatTrans.ext
  funext X
  apply Sigma.hom_ext
  intro s
  ext (r : (ringAbelianPresheaf O).obj X)
  have hL : (Functor.copowerMap (Functor.whiskerRight a
          (forget₂ RingCat.{u} AddCommGrpCat.{u})) (𝟙 F)).app X
        (Sigma.ι (fun _ : F.obj X => (ringAbelianPresheaf O).obj X) s r) =
      Sigma.ι (fun _ : F.obj X => (ringAbelianPresheaf O').obj X) s
        ((Functor.whiskerRight a (forget₂ RingCat.{u} AddCommGrpCat.{u})).app X r) := by
    have h := ConcreteCategory.congr_hom (Functor.ι_copowerMap_app
      (Functor.whiskerRight a (forget₂ RingCat.{u} AddCommGrpCat.{u})) (𝟙 F) X s) r
    simpa only [CategoryTheory.comp_apply, NatTrans.id_app, CategoryTheory.id_apply] using h
  have hM := ConcreteCategory.congr_hom (ι_freeCopowerIsoApp_hom O F X s) r
  have hN := ConcreteCategory.congr_hom (ι_freeCopowerIsoApp_hom O' F X s)
    ((Functor.whiskerRight a (forget₂ RingCat.{u} AddCommGrpCat.{u})).app X r)
  have hid : ∀ y, ((PresheafOfModules.restrictScalarsCompToPresheaf.{u} a).hom.app
      ((PresheafOfModules.free.{u} O').obj F)).app X y = y := fun _ => rfl
  simp only [CategoryTheory.comp_apply] at hM hN
  simp only [NatTrans.comp_app, CategoryTheory.comp_apply, freeCopowerIso_hom_app]
  rw [hL, hN, hM, hid]
  exact freeExtendScalarsUnit_single a F X s r

end FreeExtendScalars

/-! ### The generator step of [Stacks, Tag 08RX], on Moore complexes -/

section Generator

variable {C : Type u} [SmallCategory C] (U : CosimplicialObject C)

/-- **A morphism of abelian presheaves is a quasi-isomorphism on the extended Moore complexes of
its evaluation on a cosimplicial object exactly when the homology of the Moore complex inverts it
in every degree.** The reindexing along `ComplexShape.embeddingUpIntLE 0` that places the
simplicial degree `n` in cohomological degree `-n` changes no homology group, and the cochain
complex vanishes outside the image of that embedding.

This is the translation the module docstring of
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CoefficientQuasiIsomorphism` asks for:
the generator step recorded there is stated for `Functor.leftDerived n` of the colimit, whereas
the criterion `Stacks.ChaoticSite.AbelianValued.isIso_totalDerivedColimit_single_map_iff` is
stated for the extended Moore complex. -/
lemma quasiIso_mooreCochainComplex_map_iff {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (θ : F ⟶ G) :
    QuasiIso ((AbelianValued.mooreCochainComplex U).map θ) ↔
      ∀ n : ℕ, IsIso ((mooreHomologyFunctor AddCommGrpCat.{u} n).map
        (Functor.whiskerLeft U.op θ)) :=
  AlgebraicTopology.quasiIso_alternatingFaceMapCochainComplex_map_iff _

/-- **The generator step of [Stacks, Tag 08RX] on extended Moore complexes.** Let `U_•` be a
cosimplicial point resolution of a small category `C` with the chaotic topology and let
`θ : ℱ ⟶ 𝒢` be a morphism of abelian presheaves inverted by `L_nπ_!` in every degree. Then for
every object `W` the induced morphism of copowers by the presheaf represented by `W` — that is,
of the extensions by zero `j_{W!}ℱ_W ⟶ j_{W!}𝒢_W` — is a quasi-isomorphism on the extended Moore
complex of its evaluation on `U_•`.

Nothing about copowers is reproved: this is
`Stacks.ChaoticSite.isIso_leftDerivedColimit_map_copowerMap` read through
`Stacks.ChaoticSite.quasiIso_mooreCochainComplex_map_iff` and the degreewise form of
[Stacks, Tag 08Q9]. -/
theorem quasiIso_mooreCochainComplex_map_copowerMap (hU : IsPointResolution U) (W : C)
    {F G : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (θ : F ⟶ G)
    (hθ : ∀ n, IsIso (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived
      n).map θ)) :
    QuasiIso ((AbelianValued.mooreCochainComplex U).map
      (Functor.copowerMap θ (𝟙 (yoneda.obj W)))) := by
  rw [quasiIso_mooreCochainComplex_map_iff]
  intro n
  exact (isIso_leftDerivedColimit_map_iff U hU _ n).1
    (isIso_leftDerivedColimit_map_copowerMap U hU W θ hθ n)

/-- **The column step of [Stacks, Tag 08RX] at the generators.** Let `C` be a small category with
the chaotic topology, let `U_•` be a cosimplicial point resolution of `C` and let `a : 𝒪 ⟶ 𝒪'` be
a morphism of presheaves of rings whose underlying morphism of abelian presheaves is inverted by
`L_nπ_!` in every degree. Then, for every object `W` of `C`, the unit
`j_{W!}𝒪_W ⟶ j_{W!}𝒪_W ⊗_𝒪 𝒪'` of the change-of-coefficients adjunction at the generator
`j_{W!}𝒪_W = 𝒪⟨h_W⟩` is a quasi-isomorphism on the extended Moore complex of its evaluation on
`U_•`.

This is the hypothesis on the columns that the dévissage of [Stacks, Tag 08RX] consumes, and it is
unconditional in the coefficient map: no flatness is discharged, because on a chaotic site the
generator is the free module on a representable. The proof identifies the unit at the generator
with the copower of `a` (`Stacks.ChaoticSite.freeCopowerIso_hom_comp_map_freeExtendScalarsUnit`),
up to isomorphisms of source and target, and then applies
`Stacks.ChaoticSite.quasiIso_mooreCochainComplex_map_copowerMap`. -/
theorem quasiIso_mooreCochainComplex_map_unit_free (hU : IsPointResolution U)
    {O O' : Cᵒᵖ ⥤ RingCat.{u}} (a : O ⟶ O') (W : C)
    (ha : ∀ n, IsIso (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived
      n).map (Functor.whiskerRight a (forget₂ RingCat.{u} AddCommGrpCat.{u})))) :
    QuasiIso ((AbelianValued.mooreCochainComplex U).map
      ((PresheafOfModules.toPresheaf O).map ((changeOfRingsAdjunction a).unit.app
        ((PresheafOfModules.free.{u} O).obj (yoneda.obj W))))) := by
  have hcop : QuasiIso ((AbelianValued.mooreCochainComplex U).map
      (Functor.copowerMap (Functor.whiskerRight a
        (forget₂ RingCat.{u} AddCommGrpCat.{u})) (𝟙 (yoneda.obj W)))) :=
    quasiIso_mooreCochainComplex_map_copowerMap U hU W _ ha
  have hq : QuasiIso ((AbelianValued.mooreCochainComplex U).map
      ((freeCopowerIso O (yoneda.obj W)).hom ≫
        (PresheafOfModules.toPresheaf O).map (freeExtendScalarsUnit a (yoneda.obj W)) ≫
        (PresheafOfModules.restrictScalarsCompToPresheaf.{u} a).hom.app
          ((PresheafOfModules.free.{u} O').obj (yoneda.obj W)))) := by
    rw [freeCopowerIso_hom_comp_map_freeExtendScalarsUnit a (yoneda.obj W), Functor.map_comp]
    infer_instance
  rw [Functor.map_comp, Functor.map_comp] at hq
  have h2 := quasiIso_of_comp_left _ _ (hφφ' := hq)
  have h3 := quasiIso_of_comp_right _ _ (hφφ' := h2)
  simp only [freeExtendScalarsUnit, Functor.map_comp] at h3
  exact quasiIso_of_comp_right _ _ (hφφ' := h3)

end Generator

/-! ### Bookkeeping for invertibility along a commutative square -/

section Bookkeeping

/-- **Two morphisms with a common source that agree after composing with invertible morphisms
are invertible together.** This is the elementary step used repeatedly below to move the
question of invertibility of a comparison map across an identification of its target. -/
lemma isIso_iff_isIso_of_comp_eq {D : Type*} [Category* D] {X Y Z W : D} {f : X ⟶ Y}
    {g : Y ⟶ Z} {f' : X ⟶ W} {g' : W ⟶ Z} (hg : IsIso g) (hg' : IsIso g')
    (h : f ≫ g = f' ≫ g') : IsIso f ↔ IsIso f' :=
  ⟨fun _ => IsIso.of_isIso_fac_right h.symm, fun _ => IsIso.of_isIso_fac_right h⟩

/-- **The same, for a square whose other two sides are an invertible morphism of sources and an
invertible morphism of targets**: if `f ≫ g = u ≫ f'` with `g` and `u` invertible then `f` is
invertible exactly when `f'` is. -/
lemma isIso_iff_isIso_of_comp_eq_comp {D : Type*} [Category* D] {X Y Z W : D} {f : X ⟶ Y}
    {g : Y ⟶ Z} {u : X ⟶ W} {f' : W ⟶ Z} (hg : IsIso g) (hu : IsIso u)
    (h : f ≫ g = u ≫ f') : IsIso f ↔ IsIso f' :=
  ⟨fun _ => IsIso.of_isIso_fac_left h.symm, fun _ => IsIso.of_isIso_fac_right h⟩

/-- A functor inverts `f` exactly when it inverts `f'`, for a square `f ≫ g = u ≫ f'` whose
sides `g` and `u` are invertible. -/
private lemma isIso_map_iff_of_comp_eq_comp {D E : Type*} [Category* D] [Category* E] (Φ : D ⥤ E)
    {X Y Z W : D} {f : X ⟶ Y} {g : Y ⟶ Z} {u : X ⟶ W} {f' : W ⟶ Z} (hg : IsIso g)
    (hu : IsIso u) (h : f ≫ g = u ≫ f') : IsIso (Φ.map f) ↔ IsIso (Φ.map f') :=
  isIso_iff_isIso_of_comp_eq_comp (Φ.map_isIso g) (Φ.map_isIso u)
    (by rw [← Φ.map_comp, ← Φ.map_comp, h])

/-- **Whether a functor inverts the component of a transformation out of the identity depends
only on the isomorphism class of the object.** This is the naturality square of `u` at an
isomorphism, whose two other sides are sent to isomorphisms by `Φ`. It is what lets the
invertibility of the change-of-coefficients comparison at a complex be checked on a projective
resolution of that complex. -/
lemma isIso_map_app_iff_of_iso {D E : Type*} [Category* D] [Category* E] {G : D ⥤ D}
    (u : 𝟭 D ⟶ G) (Φ : D ⥤ E) {X Y : D} (e : X ≅ Y) :
    IsIso (Φ.map (u.app X)) ↔ IsIso (Φ.map (u.app Y)) := by
  have hnat : u.app X ≫ G.map e.hom = e.hom ≫ u.app Y := by
    simpa using (u.naturality e.hom).symm
  exact isIso_map_iff_of_comp_eq_comp Φ (G.mapIso e).isIso_hom e.isIso_hom hnat

end Bookkeeping

/-! ### From the generators to an arbitrary projective presheaf of modules -/

section Coproducts

variable {C : Type u} [SmallCategory C] (U : CosimplicialObject C)

/-- **The extended Moore complex of the evaluation on a cosimplicial object preserves
colimits.** Colimits of complexes are computed degreewise, and in each cohomological degree the
functor is either evaluation of the abelian presheaf at an object of the site or zero; this is
`AlgebraicTopology.preservesColimitsOfShape_alternatingFaceMapCochainComplex` composed with
evaluation on `U_•`, which is itself computed degreewise.

Coproducts are the case of interest: the dévissage of [Stacks, Tag 08RX] passes from the
generators `j_{W!}𝒪_W` to the coproducts of generators that cover an arbitrary presheaf of
modules, and `CochainComplex.quasiIso_app_sigma` needs both sides of the comparison to take
coproducts to coproducts. -/
instance AbelianValued.preservesColimitsOfShape_mooreCochainComplex {J : Type*} [Category* J]
    [HasColimitsOfShape J AddCommGrpCat.{u}] :
    PreservesColimitsOfShape J (AbelianValued.mooreCochainComplex U) :=
  inferInstanceAs (PreservesColimitsOfShape J
    ((Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ AddCommGrpCat.{u}).obj U.op ⋙
      AlgebraicTopology.alternatingFaceMapCochainComplex AddCommGrpCat.{u}))

variable {O O' : Cᵒᵖ ⥤ RingCat.{u}} (a : O ⟶ O')

/-- **The change-of-coefficients unit on extended Moore complexes**, as a natural transformation
of functors of the `𝒪`-module: it sends `M` to the map of extended Moore complexes of the
evaluation on `U_•` induced by the unit `M ⟶ M ⊗_𝒪 𝒪'`, read on underlying abelian presheaves.

The target is spelled with `PresheafOfModules.toPresheaf 𝒪'` rather than with restriction of
scalars followed by `PresheafOfModules.toPresheaf 𝒪`: restriction of scalars does not change the
underlying abelian presheaf, `PresheafOfModules.restrictScalarsCompToPresheaf` being the identity
isomorphism, so the two readings are the same functor and this one takes coproducts to coproducts
for formal reasons. -/
def mooreCochainUnit :
    PresheafOfModules.toPresheaf.{u} O ⋙ AbelianValued.mooreCochainComplex U ⟶
      extendScalars a ⋙ PresheafOfModules.toPresheaf.{u} O' ⋙
        AbelianValued.mooreCochainComplex U :=
  Functor.whiskerRight (Functor.whiskerRight (changeOfRingsAdjunction a).unit
    (PresheafOfModules.toPresheaf.{u} O)) (AbelianValued.mooreCochainComplex U)

/-- The components of `Stacks.ChaoticSite.mooreCochainUnit`. -/
lemma mooreCochainUnit_app (M : PresheafOfModules.{u} O) :
    (mooreCochainUnit U a).app M =
      (AbelianValued.mooreCochainComplex U).map
        ((PresheafOfModules.toPresheaf.{u} O).map
          ((changeOfRingsAdjunction a).unit.app M)) :=
  rfl

/-- **The coproduct step of the dévissage of [Stacks, Tag 08RX]**: if the change-of-coefficients
unit is a quasi-isomorphism on extended Moore complexes at every member of a family of
`𝒪`-modules, then it is one at their coproduct.

This is `CochainComplex.quasiIso_app_sigma`, Grothendieck's axiom AB4 for quasi-isomorphisms
together with the fact that both sides of `Stacks.ChaoticSite.mooreCochainUnit` preserve
coproducts. -/
theorem quasiIso_mooreCochainUnit_app_sigma {I : Type u} (N : I → PresheafOfModules.{u} O)
    (hN : ∀ i, QuasiIso ((mooreCochainUnit U a).app (N i))) :
    QuasiIso ((mooreCochainUnit U a).app (∐ N)) :=
  CochainComplex.quasiIso_app_sigma (mooreCochainUnit U a) N hN

/-- **The change-of-coefficients unit is a quasi-isomorphism on extended Moore complexes at the
canonical cover of an `𝒪`-module by free modules on representables.** The cover
`PresheafOfModules.freeYonedaCoproduct` is the coproduct, indexed by the elements of the module,
of the generators `j_{W!}𝒪_W = 𝒪⟨h_W⟩` of the proof of [Stacks, Tag 08RX]; the unit is a
quasi-isomorphism at each summand by
`Stacks.ChaoticSite.quasiIso_mooreCochainComplex_map_unit_free`, and
`Stacks.ChaoticSite.quasiIso_mooreCochainUnit_app_sigma` assembles the summands. -/
theorem quasiIso_mooreCochainUnit_app_freeYonedaCoproduct (hU : IsPointResolution U)
    (ha : ∀ n, IsIso (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived
      n).map (Functor.whiskerRight a (forget₂ RingCat.{u} AddCommGrpCat.{u}))))
    (M : PresheafOfModules.{u} O) :
    QuasiIso ((mooreCochainUnit U a).app M.freeYonedaCoproduct) :=
  quasiIso_mooreCochainUnit_app_sigma U a _ fun m =>
    quasiIso_mooreCochainComplex_map_unit_free U hU a m.1.unop ha

/-- **The retract step of the dévissage of [Stacks, Tag 08RX]**: the change-of-coefficients unit
is a quasi-isomorphism on extended Moore complexes at every *projective* presheaf of modules.

A projective presheaf of modules is a retract of its canonical cover by free modules on
representables, the structure morphism `PresheafOfModules.fromFreeYonedaCoproduct` being an
epimorphism; `CategoryTheory.NatTrans.retractArrowApp` turns that retract into a retract of
arrows, and quasi-isomorphisms of complexes of abelian groups are stable under retracts. -/
theorem quasiIso_mooreCochainUnit_app_of_projective (hU : IsPointResolution U)
    (ha : ∀ n, IsIso (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived
      n).map (Functor.whiskerRight a (forget₂ RingCat.{u} AddCommGrpCat.{u}))))
    (N : PresheafOfModules.{u} O) [Projective N] :
    QuasiIso ((mooreCochainUnit U a).app N) := by
  have hs : Projective.factorThru (𝟙 N) N.fromFreeYonedaCoproduct ≫
      N.fromFreeYonedaCoproduct = 𝟙 N := Projective.factorThru_comp _ _
  rw [← HomologicalComplex.mem_quasiIso_iff]
  exact MorphismProperty.of_retract
    (NatTrans.retractArrowApp (mooreCochainUnit U a)
      { i := Projective.factorThru (𝟙 N) N.fromFreeYonedaCoproduct
        r := N.fromFreeYonedaCoproduct
        retract := hs })
    ((HomologicalComplex.mem_quasiIso_iff _).2
      (quasiIso_mooreCochainUnit_app_freeYonedaCoproduct U a hU ha N))

end Coproducts

/-! ### The change of coefficients of [Stacks, Tag 08QJ] -/

section CoefficientChange

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] (U : CosimplicialObject C)

/-- **Derived lower shriek inverts a morphism of bounded above complexes of abelian presheaves
which is a quasi-isomorphism on the extended Moore complexes in every degree.** This is
[Stacks, Tag 0133] for the Moore double complex of such a complex, with the hypothesis on the
columns: the comparison `Stacks.ChaoticSite.AbelianValued.totalQIsoDerivedColimitOfResolution`
identifies `Lπ_!` of a bounded above complex with the total complex of its Moore double complex,
naturally in the complex, and the columnwise hypothesis makes the induced map of total complexes
a quasi-isomorphism.

The projective resolutions of the two complexes needed to form the comparison are the ones of
[Stacks, Tag 0646], `ProjectiveResolutionLemma.statement3`; the naturality does not depend on
the choice, because the resolution of the target is degreewise epimorphic. -/
theorem AbelianValued.isIso_totalDerivedColimit_map_of_quasiIso_columns
    (hU : IsPointResolution U) {K L : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℤ}
    [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (ψ : K ⟶ L)
    (hψ : ∀ p, QuasiIso ((AbelianValued.mooreCochainComplex U).map (ψ.f p))) :
    IsIso ((Stacks.CategoryHomology.totalDerivedColimit C AddCommGrpCat.{u}).map
      (DerivedCategory.Q.map ψ)) := by
  obtain ⟨R, hR⟩ := ProjectiveResolutionLemma.statement3 (0 : ℤ) K inferInstance
  obtain ⟨S, hS⟩ := ProjectiveResolutionLemma.statement3 (0 : ℤ) L inferInstance
  have := R.projective
  have := R.boundedAbove
  have := R.quasiIso
  have := S.projective
  have := S.boundedAbove
  have := S.quasiIso
  have hqi : QuasiIso (HomologicalComplex₂.total.map
      ((AbelianValued.mooreBicomplexFunctor U).map ψ) (ComplexShape.up ℤ)) :=
    StacksDraft.TotalComplexQuasiIso.quasiIso_total_map_of_upperBound _ 0 0
      (fun p hp => GeneralValued.isZero_mooreBicomplex_X U K p
        (CochainComplex.isZero_of_isStrictlyLE K 0 p hp))
      (fun p q hq => GeneralValued.isZero_mooreBicomplex_X_X U K p q hq)
      (fun p hp => GeneralValued.isZero_mooreBicomplex_X U L p
        (CochainComplex.isZero_of_isStrictlyLE L 0 p hp))
      (fun p q hq => GeneralValued.isZero_mooreBicomplex_X_X U L p q hq)
      hψ
  have h1 : IsIso (DerivedCategory.Q.map (HomologicalComplex₂.total.map
      ((AbelianValued.mooreBicomplexFunctor U).map ψ) (ComplexShape.up ℤ))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hqi
  have hcmp := AbelianValued.totalQIsoDerivedColimitOfResolution_naturality_of_epi U hU
    R.α S.α hS ψ
  have h2 : IsIso ((AbelianValued.totalQIsoDerivedColimitOfResolution U hU K R.complex R.α).hom ≫
      (Stacks.CategoryHomology.totalDerivedColimit C AddCommGrpCat.{u}).map
        (DerivedCategory.Q.map ψ)) := by
    rw [← hcmp]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (AbelianValued.totalQIsoDerivedColimitOfResolution U hU K R.complex R.α).hom _

variable {O O' : Cᵒᵖ ⥤ RingCat.{u}} (a : O ⟶ O')

/-- **The unit of the derived change-of-coefficients adjunction at a K-projective complex is the
degreewise underived unit**, in the following sense: a functor out of `D(Mod(𝒪))` inverts the one
exactly when it inverts the other.

The derived tensor product `- ⊗^L_𝒪 𝒪'` is a total left derived functor, so its comparison with
the degreewise functor is invertible at a K-projective complex
(`Stacks.Homology.isIso_leftDerivedCounit_app_of_isKProjective`), and restriction of scalars is
exact, so its degreewise derived functor factors through the localisation on the nose
(`CategoryTheory.Functor.mapDerivedCategoryFactorsh`). The identity relating the two units
through those two comparisons is `CategoryTheory.Adjunction.derivedη_fac_app`, the defining
property of the unit of a derived adjunction. -/
theorem isIso_map_derivedExtendScalarsAdjunction_unit_app_Qh_iff {E : Type*} [Category* E]
    (Φ : DerivedCategory (PresheafOfModules.{u} O) ⥤ E)
    (P : CochainComplex (PresheafOfModules.{u} O) ℤ) [P.IsKProjective] :
    IsIso (Φ.map ((derivedExtendScalarsAdjunction a).unit.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (PresheafOfModules.{u} O) (ComplexShape.up ℤ)).obj P)))) ↔
      IsIso (Φ.map (DerivedCategory.Qh.map
        (((changeOfRingsAdjunction a).mapHomotopyCategory (ComplexShape.up ℤ)).unit.app
          ((HomotopyCategory.quotient (PresheafOfModules.{u} O) (ComplexShape.up ℤ)).obj P)))) := by
  have := Stacks.CategoryHomology.hasPointwiseLeftDerivedFunctor_of_enoughProjectives
    (extendScalars a)
  have := derivedExtendScalars_isLeftDerivedFunctor a
  have := Stacks.CategoryHomology.isLeftDerivedFunctor_comp_of_enoughProjectives
    (extendScalars a) (derivedExtendScalars a) (derivedExtendScalarsCounit a)
    (PresheafOfModules.restrictScalars.{u} a).mapDerivedCategory
  have hα : IsIso ((derivedExtendScalarsCounit a).app
      ((HomotopyCategory.quotient (PresheafOfModules.{u} O) (ComplexShape.up ℤ)).obj P)) :=
    Stacks.Homology.isIso_leftDerivedCounit_app_of_isKProjective _ _ P
  have key := Adjunction.derivedη_fac_app
    ((changeOfRingsAdjunction a).mapHomotopyCategory (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso (PresheafOfModules.{u} O) (ComplexShape.up ℤ))
    (derivedExtendScalarsCounit a)
    (PresheafOfModules.restrictScalars.{u} a).mapDerivedCategoryFactorsh.inv
    ((HomotopyCategory.quotient (PresheafOfModules.{u} O) (ComplexShape.up ℤ)).obj P)
  have hunit : (derivedExtendScalarsAdjunction a).unit =
      Adjunction.derivedη ((changeOfRingsAdjunction a).mapHomotopyCategory (ComplexShape.up ℤ))
        (HomotopyCategory.quasiIso (PresheafOfModules.{u} O) (ComplexShape.up ℤ))
        (derivedExtendScalarsCounit a)
        (PresheafOfModules.restrictScalars.{u} a).mapDerivedCategoryFactorsh.inv := rfl
  rw [hunit]
  have key' := congrArg Φ.map key
  rw [Φ.map_comp, Φ.map_comp] at key'
  have := hα
  exact isIso_iff_isIso_of_comp_eq
    (Φ.mapIso ((PresheafOfModules.restrictScalars.{u} a).mapDerivedCategory.mapIso
      (asIso ((derivedExtendScalarsCounit a).app
        ((HomotopyCategory.quotient (PresheafOfModules.{u} O) (ComplexShape.up ℤ)).obj
          P))))).isIso_hom
    (Φ.mapIso ((PresheafOfModules.restrictScalars.{u} a).mapDerivedCategoryFactorsh.symm.app
      (((extendScalars a).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (PresheafOfModules.{u} O) (ComplexShape.up ℤ)).obj
          P)))).isIso_hom key'

/-- **`Stacks.ChaoticSite.isIso_map_derivedExtendScalarsAdjunction_unit_app_Qh_iff` read on the
localisation of complexes.** The image of a complex in the derived category is isomorphic to the
image of its class in the homotopy category, `DerivedCategory.quotientCompQhIso`, so the
statement transports along that isomorphism. -/
theorem isIso_map_derivedExtendScalarsAdjunction_unit_app_Q_iff {E : Type*} [Category* E]
    (Φ : DerivedCategory (PresheafOfModules.{u} O) ⥤ E)
    (P : CochainComplex (PresheafOfModules.{u} O) ℤ) [P.IsKProjective] :
    IsIso (Φ.map ((derivedExtendScalarsAdjunction a).unit.app (DerivedCategory.Q.obj P))) ↔
      IsIso (Φ.map (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (changeOfRingsAdjunction a).unit (ComplexShape.up ℤ)).app P))) := by
  refine (isIso_map_app_iff_of_iso _ Φ
      ((DerivedCategory.quotientCompQhIso (PresheafOfModules.{u} O)).app P).symm).trans
    ((isIso_map_derivedExtendScalarsAdjunction_unit_app_Qh_iff a Φ P).trans ?_)
  exact isIso_map_iff_of_comp_eq_comp Φ
    ((DerivedCategory.quotientCompQhIso (PresheafOfModules.{u} O)).app _).isIso_hom
    ((DerivedCategory.quotientCompQhIso (PresheafOfModules.{u} O)).app _).isIso_hom
    (DerivedCategory.quotientCompQhIso_hom_naturality
      ((NatTrans.mapHomologicalComplex (changeOfRingsAdjunction a).unit
        (ComplexShape.up ℤ)).app P))

/-- **The comparison of [Stacks, Tag 08QJ] is invertible at an object of `D(Mod(𝒪))` exactly
when derived lower shriek inverts the unit of the derived change-of-coefficients adjunction
there.** The remaining factor of
`Stacks.ChaoticSite.derivedColimitTensorComparison` is the identification
`Stacks.ChaoticSite.restrictScalarsDerivedColimitIso` of `Lπ_!` on `𝒪'`-modules with `Lπ_!` on
their underlying `𝒪`-modules, which is invertible. -/
lemma isIso_derivedColimitTensorComparison_app_iff
    (X : DerivedCategory (PresheafOfModules.{u} O)) :
    IsIso ((derivedColimitTensorComparison a).app X) ↔
      IsIso ((abelianDerivedColimitOfModules O).map
        ((derivedExtendScalarsAdjunction a).unit.app X)) := by
  have heq : (derivedColimitTensorComparison a).app X =
      (abelianDerivedColimitOfModules O).map
          ((derivedExtendScalarsAdjunction a).unit.app X) ≫
        (restrictScalarsDerivedColimitIso a).hom.app ((derivedExtendScalars a).obj X) := by
    dsimp [derivedColimitTensorComparison]
    rw [Category.id_comp, Category.id_comp]
  rw [heq]
  constructor
  · intro _
    exact IsIso.of_isIso_comp_right _
      ((restrictScalarsDerivedColimitIso a).hom.app ((derivedExtendScalars a).obj X))
  · intro _
    infer_instance

/-- **The change of coefficients of [Stacks, Tag 08QJ], on an arbitrary chaotic site.** Let `C`
be a small category with the chaotic topology, let `U_•` be a cosimplicial point resolution of
`C`, and let `a : 𝒪 ⟶ 𝒪'` be a morphism of presheaves of rings which derived lower shriek
inverts in every degree. Then, for every presheaf of `𝒪`-modules `ℱ` placed in cohomological
degree zero, the canonical comparison

`Lπ_!(ℱ) ⟶ Lπ_!(ℱ ⊗^L_𝒪 𝒪')`

is an isomorphism in `D(Ab)`.

This is the dévissage of [Stacks, Tag 08RX] in degree zero, carried out on Moore double
complexes rather than on homotopy colimits. The chain is: an `𝒪`-module placed in degree zero
has a resolution by a bounded above complex of projective presheaves of modules
([Stacks, Tag 0646]), so by
`Stacks.ChaoticSite.isIso_map_app_iff_of_iso` and
`Stacks.ChaoticSite.isIso_map_derivedExtendScalarsAdjunction_unit_app_Q_iff` the comparison may
be computed with the *degreewise underived* unit of that resolution; that unit is a
quasi-isomorphism on extended Moore complexes in every degree by
`Stacks.ChaoticSite.quasiIso_mooreCochainUnit_app_of_projective`; and
`Stacks.ChaoticSite.AbelianValued.isIso_totalDerivedColimit_map_of_quasiIso_columns`
turns that into invertibility after `Lπ_!`.

No `CategoryTheory.NatTrans.CommShift` on the comparison and no homotopy colimit in
`D(Mod(𝒪))` is used, which is what makes the Moore-bicomplex route available: the only
devissage performed is the one already present in
`Stacks.ChaoticSite.AbelianValued.totalQIsoDerivedColimitOfResolution`. -/
theorem isIso_derivedColimitTensorComparison_app_single (hU : IsPointResolution U)
    (ha : ∀ n, IsIso (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived
      n).map (Functor.whiskerRight a (forget₂ RingCat.{u} AddCommGrpCat.{u}))))
    (F : PresheafOfModules.{u} O) :
    IsIso ((derivedColimitTensorComparison a).app (DerivedCategory.Q.obj
      ((HomologicalComplex.single (PresheafOfModules.{u} O) (ComplexShape.up ℤ) 0).obj F))) := by
  obtain ⟨P, hP⟩ := ProjectiveResolutionLemma.statement3 (0 : ℤ)
    ((HomologicalComplex.single (PresheafOfModules.{u} O) (ComplexShape.up ℤ) 0).obj F)
    inferInstance
  have := P.projective
  have := P.boundedAbove
  have := P.quasiIso
  have hKP : P.complex.IsKProjective := CochainComplex.isKProjective_of_projective P.complex 0
  have hQ : IsIso (DerivedCategory.Q.map P.α) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 P.quasiIso
  rw [isIso_derivedColimitTensorComparison_app_iff,
    isIso_map_app_iff_of_iso _ _ (asIso (DerivedCategory.Q.map P.α)).symm,
    isIso_map_derivedExtendScalarsAdjunction_unit_app_Q_iff]
  refine (isIso_map_iff_of_comp_eq_comp
    (Stacks.CategoryHomology.totalDerivedColimit C AddCommGrpCat.{u})
    ((PresheafOfModules.toPresheaf.{u} O).mapDerivedCategoryFactors.app _).isIso_hom
    ((PresheafOfModules.toPresheaf.{u} O).mapDerivedCategoryFactors.app _).isIso_hom
    ((PresheafOfModules.toPresheaf.{u} O).mapDerivedCategoryFactors.hom.naturality
      ((NatTrans.mapHomologicalComplex (changeOfRingsAdjunction a).unit
        (ComplexShape.up ℤ)).app P.complex))).mpr
    (AbelianValued.isIso_totalDerivedColimit_map_of_quasiIso_columns U hU _
      fun p => quasiIso_mooreCochainUnit_app_of_projective U a hU ha (P.complex.X p))

end CoefficientChange

end Stacks.ChaoticSite

namespace CommAlgCat

universe u

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-! ### Objects over `B`, read as rings -/

/-- An `A`-algebra over `B`, read as a ring in `Type u`: forget the structure morphism to `B`,
then the `A`-algebra structure. -/
def overRingFunctor : Over B ⥤ RingCat.{u} :=
  Over.forget B ⋙ forget₂ (CommAlgCat.{u} A) CommRingCat.{u} ⋙
    forget₂ CommRingCat.{u} RingCat.{u}

/-- The ring underlying `B`. -/
abbrev ringOfBase : RingCat.{u} :=
  (forget₂ CommRingCat.{u} RingCat.{u}).obj ((forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).obj B)

/-- **The augmentation of an `A`-algebra over `B`**, read as a morphism of rings into `B`: the
structure morphism of the object of `Over B`. It is natural in that object, the square being the
commutativity of a morphism over `B`. -/
def overStructureAugmentation :
    overRingFunctor A B ⟶ (Functor.const (Over B)).obj (ringOfBase A B) where
  app P := (forget₂ CommRingCat.{u} RingCat.{u}).map
    ((forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).map P.hom)
  naturality P Q f := by
    have hw := congrArg
      (fun g : P.left ⟶ B => (forget₂ CommRingCat.{u} RingCat.{u}).map
        ((forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).map g)) (Over.w f)
    exact hw.trans (Category.comp_id _).symm

variable (κ : Cardinal.{u})

/-! ### The two presheaves of rings on the small model, and the augmentation -/

/-- An object of the small model of the restricted site, read as an `A`-algebra over `B`: undo the
two opposites, pass to the restricted category of polynomial augmentations through the small
model's fully faithful inclusion, and forget the polynomiality. -/
abbrev smallSiteToOver : (smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ Over B :=
  unopUnop (SmallBoundedPolynomialAugmentation A B κ) ⋙
    smallBoundedPolynomialAugmentationι A B κ ⋙ (IsPolynomialAlgebraOverBelow A B κ).ι

/-- **The tautological presheaf of rings `𝒪` on the small model of `C_{B/A}`**, sending an object
`(P, α)` to the ring `P`, with sections in `Type u`. It is a sheaf for the chaotic topology of
`C_{B/A}`, every presheaf being one. -/
def smallPolynomialStructurePresheaf :
    (smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ RingCat.{u} :=
  smallSiteToOver A B κ ⋙ overRingFunctor A B

/-- **The constant presheaf of rings `B̲` on the small model of `C_{B/A}`**, with sections in
`Type u`. -/
abbrev smallPolynomialConstantPresheaf :
    (smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ RingCat.{u} :=
  (Functor.const (smallBoundedPolynomialSite A B κ)ᵒᵖ).obj (ringOfBase A B)

/-- **The map of presheaves of rings `𝒪 ⟶ B̲` on the small model of `C_{B/A}`**, given by the
augmentations `α : P → B`. This is the morphism of coefficients whose effect on derived lower
shriek [Stacks, Tag 08QJ] describes. -/
def smallPolynomialAugmentation :
    smallPolynomialStructurePresheaf A B κ ⟶ smallPolynomialConstantPresheaf A B κ :=
  Functor.whiskerLeft (smallSiteToOver A B κ) (overStructureAugmentation A B)

/-- The augmentation evaluated at an object of the small model is the structure morphism of the
`A`-algebra that object names. -/
lemma smallPolynomialAugmentation_app (X : ((smallBoundedPolynomialSite A B κ)ᵒᵖ)) :
    (smallPolynomialAugmentation A B κ).app X =
      (forget₂ CommRingCat.{u} RingCat.{u}).map
        ((forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).map
          ((smallSiteToOver A B κ).obj X).hom) :=
  rfl

/-! ### The same two presheaves on the unrestricted site, and the two identifications -/

/-- **The tautological presheaf of rings on the unrestricted site `CommAlgCat.polynomialSite`,
with sections in `Type u`.** This is `CommAlgCat.polynomialStructurePresheaf` without the
universe lift: that one has its sections in `CommRingCat.{u + 1}`, the universe in which the
morphism of topoi `π` of [Stacks, Tag 08PR] is formed. -/
def polynomialStructurePresheafRing : (polynomialSite A B)ᵒᵖ ⥤ RingCat.{u} :=
  unopUnop (PolynomialAugmentation A B) ⋙ (IsPolynomialAlgebraOver A B).ι ⋙
    overRingFunctor A B

/-- **The map `𝒪 ⟶ B̲` on the unrestricted site**, with sections in `Type u`. -/
def polynomialAugmentationRing :
    polynomialStructurePresheafRing A B ⟶
      (Functor.const (polynomialSite A B)ᵒᵖ).obj (ringOfBase A B) :=
  Functor.whiskerLeft
    (unopUnop (PolynomialAugmentation A B) ⋙ (IsPolynomialAlgebraOver A B).ι)
    (overStructureAugmentation A B)

/-- **The structure presheaf of the small model is the restriction of the one on the unrestricted
site**, on the nose: the inclusion of the small model into the unrestricted site is, on objects,
the passage from an index to the `A`-algebra over `B` it names, which is what both sides apply
`CommAlgCat.overRingFunctor` to. -/
lemma smallPolynomialStructurePresheaf_eq :
    smallPolynomialStructurePresheaf A B κ =
      (smallBoundedPolynomialSiteToPolynomialSite A B κ).op ⋙
        polynomialStructurePresheafRing A B :=
  rfl

/-- **The augmentation of the small model is the restriction of the one on the unrestricted
site**, on the nose. -/
lemma smallPolynomialAugmentation_eq :
    smallPolynomialAugmentation A B κ =
      Functor.whiskerLeft (smallBoundedPolynomialSiteToPolynomialSite A B κ).op
        (polynomialAugmentationRing A B) :=
  rfl

/-! ### Evaluation on the cosimplicial object of a resolution -/

section Resolution

variable {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)
  (hP : ∀ n, IsPolynomialAlgebra A (P.obj n))

/-- **Evaluating the structure presheaf on the cosimplicial object of a resolution returns the
simplicial algebra itself**, read as a simplicial ring, on the nose. This is the identification
that lets the criterion of [Stacks, Tag 08QI] be read as a statement about the Moore complex of
the evaluation of `𝒪` on a point resolution. -/
lemma polynomialStructurePresheafRing_comp_resolution :
    (resolutionCosimplicialObject ε hP).op ⋙ polynomialStructurePresheafRing A B =
      P ⋙ forget₂ (CommAlgCat.{u} A) CommRingCat.{u} ⋙ forget₂ CommRingCat.{u} RingCat.{u} :=
  rfl

/-- **Evaluating the augmentation `𝒪 ⟶ B̲` on the cosimplicial object of a resolution returns the
augmentation `ε` of that resolution**, read on the underlying simplicial rings, on the nose. -/
lemma polynomialAugmentationRing_comp_resolution :
    Functor.whiskerLeft (resolutionCosimplicialObject ε hP).op
        (polynomialAugmentationRing A B) =
      Functor.whiskerRight ε
        (forget₂ (CommAlgCat.{u} A) CommRingCat.{u} ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  rfl

end Resolution

/-! ### The augmentation read on the underlying abelian presheaves -/

/-- **The map of presheaves of rings `𝒪 ⟶ B̲` read on the underlying abelian presheaves.** This is
the morphism of abelian sheaves whose derived lower shriek the second hypothesis of
[Stacks, Tag 08RX] requires to be invertible, namely `Lπ_!(𝒪) ⟶ Lπ_!(B̲)`: the derived lower
shriek of [Stacks, Tag 08Q6] takes coefficients in `AddCommGrpCat.{u}`, so the presheaves of rings
have to be forgotten to abelian presheaves before it can be applied to them. -/
abbrev smallPolynomialAugmentationAbelian :
    smallPolynomialStructurePresheaf A B κ ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u} ⟶
      smallPolynomialConstantPresheaf A B κ ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u} :=
  Functor.whiskerRight (smallPolynomialAugmentation A B κ)
    (forget₂ RingCat.{u} AddCommGrpCat.{u})

/-! ### Evaluation on a bounded resolution, in the small model -/

section BoundedResolution

open AlgebraicTopology

variable {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)
  (hPκ : ∀ n, IsPolynomialAlgebraBelow A κ (P.obj n))

/-- **`𝒪(P_•, ε) ≅ P_•` in the small model of `C_{B/A}`.** Evaluating the tautological presheaf of
rings on the cosimplicial object of a resolution `ε : P_• ⟶ B` whose terms are polynomial algebras
on at most `κ` variables, read in the small model of the restricted site, returns the simplicial
ring underlying `P_•`.

On the unrestricted site this is an equality,
`CommAlgCat.polynomialStructurePresheafRing_comp_resolution`. In the small model it is a genuine
comparison isomorphism: the objects of the model are only isomorphic to the terms of the
resolution, and the transport is the restriction of `CommAlgCat.smallResolutionCosimplicialObjectι`
to `𝒪`, exactly as `CommAlgCat.smallResolutionCotangentModuleIso` is its restriction to
`i^*Ω_{𝒪/A}`. -/
def smallResolutionStructureRingIso :
    (smallResolutionCosimplicialObject ε κ hPκ).op ⋙ smallPolynomialStructurePresheaf A B κ ≅
      P ⋙ forget₂ (CommAlgCat.{u} A) CommRingCat.{u} ⋙ forget₂ CommRingCat.{u} RingCat.{u} :=
  Functor.isoWhiskerRight (NatIso.op (smallResolutionCosimplicialObjectι ε κ hPκ)).symm
    (polynomialStructurePresheafRing A B)

/-- **Evaluating the augmentation `𝒪 ⟶ B̲` on the cosimplicial object of a bounded resolution
returns the augmentation `ε` of that resolution**, read in the small model of the restricted site
and transported along `CommAlgCat.smallResolutionStructureRingIso`. Only the source needs
transporting: `B̲` is constant, so both sides have the constant simplicial ring on `B` as their
target, on the nose.

The proof is the naturality of `CommAlgCat.polynomialAugmentationRing` at the comparison morphism
of `CommAlgCat.smallResolutionCosimplicialObjectι`, the other leg of the naturality square being
the identity because `B̲` is constant, together with
`CommAlgCat.polynomialAugmentationRing_comp_resolution`, which says that the augmentation
evaluated at the cosimplicial object of the resolution is `ε` itself. -/
lemma smallPolynomialAugmentation_comp_resolution :
    Functor.whiskerLeft (smallResolutionCosimplicialObject ε κ hPκ).op
        (smallPolynomialAugmentation A B κ) =
      (smallResolutionStructureRingIso A B κ ε hPκ).hom ≫
        Functor.whiskerRight ε
          (forget₂ (CommAlgCat.{u} A) CommRingCat.{u} ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  NatTrans.ext (funext fun n =>
    (((polynomialAugmentationRing A B).naturality
      ((NatIso.op (smallResolutionCosimplicialObjectι ε κ hPκ)).symm.hom.app n)).trans
        (Category.comp_id _)).symm)

/-- **The augmentation `𝒪 ⟶ B̲` becomes a quasi-isomorphism on the Moore complex of a bounded
resolution.** Let `ε : P_• ⟶ B` be a resolution of `B` over `A` whose terms are polynomial
algebras on at most `κ` variables and whose augmentation is surjective in every degree. Then the
map of extended Moore complexes that `𝒪 ⟶ B̲` induces on the cosimplicial object of `ε` in the
small model of `C_{B/A}` is a quasi-isomorphism.

This is the second hypothesis of [Stacks, Tag 08RX] in the form in which the derived criterion of
[Stacks, Tag 08Q9] asks for it, `Stacks.ChaoticSite.AbelianValued.mooreCochainComplex` being the
Moore complex of the evaluation of an abelian presheaf on the cosimplicial object, read as a
cochain complex over `ℤ` with simplicial degree `n` in cohomological degree `-n`.

Nothing about resolutions is reproved. The criterion of [Stacks, Tag 08QI],
`CommAlgCat.isResolution_quasiIso_homotopyEquivalence_tfae`, says that `ε` is a resolution exactly
when the associated complex of `P_•` is quasi-isomorphic to the constant complex on `B`;
`CommAlgCat.smallPolynomialAugmentation_comp_resolution` identifies the map induced by `𝒪 ⟶ B̲`
with that one up to an isomorphism of its source, and quasi-isomorphisms are stable both under
composition with an isomorphism and under the reindexing along
`ComplexShape.embeddingUpIntLE (0 : ℤ)` that places the Moore complex in nonpositive degrees. The
two routes from `CommAlgCat.{u} A` to `AddCommGrpCat.{u}` — through `CommRingCat` and `RingCat`,
which is how `𝒪` is built, and through `AlgCat A` and `ModuleCat A`, which is how
[Stacks, Tag 08QI] is stated — are the same functor on the nose, so no further comparison
enters. -/
theorem quasiIso_mooreCochainComplex_map_smallPolynomialAugmentation
    (hres : IsResolution A B P ε)
    (hε : ∀ n, Function.Surjective ((ε.app n).hom)) :
    QuasiIso ((Stacks.ChaoticSite.AbelianValued.mooreCochainComplex
      (smallResolutionCosimplicialObject ε κ hPκ)).map
        (smallPolynomialAugmentationAbelian A B κ)) := by
  have h₀ : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
      (Functor.whiskerRight ε (forget₂ (CommAlgCat.{u} A) (AlgCat.{u} A) ⋙
        forget₂ (AlgCat.{u} A) (ModuleCat.{u} A) ⋙
        forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}))) :=
    ((isResolution_quasiIso_homotopyEquivalence_tfae A B P ε
      (fun n => (hPκ n).isPolynomialAlgebra) hε).out 1 2).mp hres
  have h08QI : QuasiIso
      (((Functor.whiskeringRight SimplexCategoryᵒᵖ RingCat.{u} AddCommGrpCat.{u}).obj
            (forget₂ RingCat.{u} AddCommGrpCat.{u}) ⋙
          alternatingFaceMapComplex AddCommGrpCat.{u}).map
        (Functor.whiskerRight ε
          (forget₂ (CommAlgCat.{u} A) CommRingCat.{u} ⋙
            forget₂ CommRingCat.{u} RingCat.{u}))) := h₀
  have hcomp : QuasiIso ((Stacks.ChaoticSite.cosimplicialMooreComplex
      (smallResolutionCosimplicialObject ε κ hPκ)).map
        (smallPolynomialAugmentationAbelian A B κ)) := by
    have key : (Stacks.ChaoticSite.cosimplicialMooreComplex
          (smallResolutionCosimplicialObject ε κ hPκ)).map
            (smallPolynomialAugmentationAbelian A B κ) =
        ((Functor.whiskeringRight SimplexCategoryᵒᵖ RingCat.{u} AddCommGrpCat.{u}).obj
              (forget₂ RingCat.{u} AddCommGrpCat.{u}) ⋙
            alternatingFaceMapComplex AddCommGrpCat.{u}).map
            (smallResolutionStructureRingIso A B κ ε hPκ).hom ≫
          ((Functor.whiskeringRight SimplexCategoryᵒᵖ RingCat.{u} AddCommGrpCat.{u}).obj
              (forget₂ RingCat.{u} AddCommGrpCat.{u}) ⋙
            alternatingFaceMapComplex AddCommGrpCat.{u}).map
            (Functor.whiskerRight ε
              (forget₂ (CommAlgCat.{u} A) CommRingCat.{u} ⋙
                forget₂ CommRingCat.{u} RingCat.{u})) := by
      rw [← Functor.map_comp, ← smallPolynomialAugmentation_comp_resolution A B κ ε hPκ]
      rfl
    rw [key]
    exact quasiIso_comp (hφ' := h08QI) _ _
  exact (HomologicalComplex.quasiIso_extendMap_iff _
    (ComplexShape.embeddingUpIntLE (0 : ℤ))).2 hcomp

end BoundedResolution

/-! ### `Lπ_!(𝒪) = Lπ_!(B̲)` at the small model of `C_{B/A}` -/

section Standard

attribute [local instance] HasDerivedCategory.standard

/-- **`Lπ_!(𝒪) = Lπ_!(B̲)` on the small model of `C_{B/A}`**: derived lower shriek inverts the
augmentation `𝒪 ⟶ B̲`, read on the underlying abelian presheaves and on the small model at the
cardinal `CommAlgCat.standardResolutionVarCardinal A B` bounding the standard resolution.

This is the second of the two hypotheses of [Stacks, Tag 08RX]; the first is
`CommAlgCat.isPointResolution_standardResolutionSmallCosimplicialObject`, which is
[Stacks, Tag 08PS] at that model. The bridge from the quasi-isomorphism of Moore complexes to
invertibility in `D(Ab)` is
`Stacks.ChaoticSite.AbelianValued.isIso_totalDerivedColimit_single_map_iff`, the derived form of
[Stacks, Tag 08Q9]: derived lower shriek inverts a morphism of abelian presheaves placed in degree
zero exactly when the induced morphism of extended Moore complexes of its evaluation on a point
resolution is a quasi-isomorphism. -/
theorem isIso_totalDerivedColimit_smallPolynomialAugmentation :
    IsIso ((Stacks.CategoryHomology.totalDerivedColimit
        (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))
        AddCommGrpCat.{u}).map
      (DerivedCategory.Q.map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
          (smallPolynomialAugmentationAbelian A B (standardResolutionVarCardinal A B))))) := by
  have hε : ∀ n : SimplexCategoryᵒᵖ,
      Function.Surjective (((standardResolution.{u, u} A B).hom.app n).hom) := fun n => by
    have hn : n = op (SimplexCategory.mk n.unop.len) := by rw [SimplexCategory.mk_len]
    rw [hn]
    exact surjective_standardResolution_augmentation A B n.unop.len
  exact (Stacks.ChaoticSite.AbelianValued.isIso_totalDerivedColimit_single_map_iff
      (standardResolutionSmallCosimplicialObject A B)
      (isPointResolution_standardResolutionSmallCosimplicialObject A B) _).2
    (quasiIso_mooreCochainComplex_map_smallPolynomialAugmentation A B
      (standardResolutionVarCardinal A B) (standardResolution.{u, u} A B).hom
      (standardResolution_isPolynomialAlgebraBelow A B)
      (standardResolution_isResolution.{u, u} A B) hε)

/-- **`L_nπ_!` inverts the augmentation `𝒪 ⟶ B̲` in every degree**, on the small model of
`C_{B/A}` at the cardinal `CommAlgCat.standardResolutionVarCardinal A B` bounding the standard
resolution, with `Lπ_!` read degreewise as the left derived functors of the colimit over the
index category, which is the `π_!` of [Stacks, Tag 08PF].

This is the degreewise form of `CommAlgCat.isIso_totalDerivedColimit_smallPolynomialAugmentation`.
Nothing is reproved: the derived form of [Stacks, Tag 08Q9],
`Stacks.ChaoticSite.AbelianValued.isIso_totalDerivedColimit_single_map_iff`, turns invertibility
in `D(Ab)` into a quasi-isomorphism of extended Moore complexes; the reindexing along
`ComplexShape.embeddingUpIntLE (0 : ℤ)` that places the Moore complex in nonpositive degrees
reflects quasi-isomorphisms, so the Moore complex of the evaluation on the standard resolution is
itself a quasi-isomorphism; and the degreewise form of [Stacks, Tag 08Q9],
`Stacks.ChaoticSite.isIso_leftDerivedColimit_map_iff`, reads that degree by degree. -/
theorem isIso_leftDerivedColimit_map_smallPolynomialAugmentationAbelian (n : ℕ) :
    IsIso (((colim : ((smallBoundedPolynomialSite A B
            (standardResolutionVarCardinal A B))ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
          AddCommGrpCat.{u}).leftDerived n).map
      (smallPolynomialAugmentationAbelian A B (standardResolutionVarCardinal A B))) := by
  have hq : QuasiIso ((Stacks.ChaoticSite.AbelianValued.mooreCochainComplex
      (standardResolutionSmallCosimplicialObject A B)).map
        (smallPolynomialAugmentationAbelian A B (standardResolutionVarCardinal A B))) :=
    (Stacks.ChaoticSite.AbelianValued.isIso_totalDerivedColimit_single_map_iff
        (standardResolutionSmallCosimplicialObject A B)
        (isPointResolution_standardResolutionSmallCosimplicialObject A B) _).1
      (isIso_totalDerivedColimit_smallPolynomialAugmentation A B)
  have hq' : QuasiIso ((Stacks.ChaoticSite.cosimplicialMooreComplex
      (standardResolutionSmallCosimplicialObject A B)).map
        (smallPolynomialAugmentationAbelian A B (standardResolutionVarCardinal A B))) :=
    (HomologicalComplex.quasiIso_extendMap_iff _
      (ComplexShape.embeddingUpIntLE (0 : ℤ))).1 hq
  exact (Stacks.ChaoticSite.isIso_leftDerivedColimit_map_iff _
    (isPointResolution_standardResolutionSmallCosimplicialObject A B) _ n).2
      ((quasiIsoAt_iff_isIso_homologyMap _ n).mp (hq'.quasiIsoAt n))

/-- **The generator step of [Stacks, Tag 08RX] for the augmentation `𝒪 ⟶ B̲` of the small model of
`C_{B/A}`, with no hypothesis left undischarged**: for every object `W` of the model and every
`n`, the degree `n` left derived functor of the colimit over the index category inverts the map
of extensions by zero `j_{W!}𝒪_W ⟶ j_{W!}B̲_W`, which on a chaotic site is the copower by the
presheaf represented by `W` of the augmentation read on the underlying abelian presheaves.

The hypothesis of `Stacks.ChaoticSite.isIso_leftDerivedColimit_map_copowerMap` — that `L_nπ_!`
invert the augmentation itself in every degree — is discharged by
`CommAlgCat.isIso_leftDerivedColimit_map_smallPolynomialAugmentationAbelian`, so the statement
below assumes nothing. No flatness enters either: on a chaotic site the generator `j_{W!}𝒪_W` is
the free module on a representable, hence projective
(`PresheafOfModules.freeYonedaProjective`). -/
theorem isIso_leftDerivedColimit_map_extensionByZero_smallPolynomialAugmentation
    (W : smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)) (n : ℕ) :
    IsIso (((colim : ((smallBoundedPolynomialSite A B
            (standardResolutionVarCardinal A B))ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
          AddCommGrpCat.{u}).leftDerived n).map
      (Functor.copowerMap
        (smallPolynomialAugmentationAbelian A B (standardResolutionVarCardinal A B))
        (𝟙 (yoneda.obj W)))) :=
  Stacks.ChaoticSite.isIso_leftDerivedColimit_map_copowerMap _
    (isPointResolution_standardResolutionSmallCosimplicialObject A B) W _
    (isIso_leftDerivedColimit_map_smallPolynomialAugmentationAbelian A B) n

/-- **The column step of [Stacks, Tag 08RX] for the augmentation `𝒪 ⟶ B̲` of the small model of
`C_{B/A}`, with no hypothesis left undischarged**: for every object `W` of the model, the unit
`j_{W!}𝒪_W ⟶ j_{W!}𝒪_W ⊗_𝒪 B̲` of the change-of-coefficients adjunction at the generator
`j_{W!}𝒪_W = 𝒪⟨h_W⟩` becomes a quasi-isomorphism on the extended Moore complex of its evaluation
on the standard resolution.

This is the hypothesis on the columns that the dévissage of [Stacks, Tag 08RX] consumes in order
to pass from the generators to an arbitrary complex of `𝒪`-modules, and hence what the change of
coefficients of [Stacks, Tag 08QJ] rests on at the generators. The two inputs are
`CommAlgCat.isIso_leftDerivedColimit_map_smallPolynomialAugmentationAbelian`, which is
`Lπ_!(𝒪) = Lπ_!(B̲)` read degreewise, and
`CommAlgCat.isPointResolution_standardResolutionSmallCosimplicialObject`, which is
[Stacks, Tag 08PS] at this model; neither is assumed. -/
theorem quasiIso_mooreCochainComplex_map_unit_free_smallPolynomialAugmentation
    (W : smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)) :
    QuasiIso ((Stacks.ChaoticSite.AbelianValued.mooreCochainComplex
        (standardResolutionSmallCosimplicialObject A B)).map
      ((PresheafOfModules.toPresheaf
          (smallPolynomialStructurePresheaf A B (standardResolutionVarCardinal A B))).map
        ((Stacks.ChaoticSite.changeOfRingsAdjunction
            (smallPolynomialAugmentation A B (standardResolutionVarCardinal A B))).unit.app
          ((PresheafOfModules.free.{u}
            (smallPolynomialStructurePresheaf A B
              (standardResolutionVarCardinal A B))).obj (yoneda.obj W))))) :=
  Stacks.ChaoticSite.quasiIso_mooreCochainComplex_map_unit_free
    (standardResolutionSmallCosimplicialObject A B)
    (isPointResolution_standardResolutionSmallCosimplicialObject A B)
    (smallPolynomialAugmentation A B (standardResolutionVarCardinal A B)) W
    (isIso_leftDerivedColimit_map_smallPolynomialAugmentationAbelian A B)

/-- **The change of coefficients of [Stacks, Tag 08QJ].** Let `A → B` be a ring map and let
`𝒪`, `B̲` and `π` be as in [Stacks, Tag 08PR], read on the small model of `C_{B/A}` at the
cardinal `CommAlgCat.standardResolutionVarCardinal A B` bounding the standard resolution. Then
for every `𝒪`-module `ℱ`, placed in cohomological degree zero, the canonical comparison

`Lπ_!(ℱ) ⟶ Lπ_!(ℱ ⊗^L_𝒪 B̲)`

is an isomorphism in `D(Ab)`.

The source states the right-hand side as `Lπ_!(Li^*ℱ)` for the morphism of topoi `i` attached to
the ring map `B ⟶ B`; on a chaotic site that morphism is the identity on topoi, so `Li^*ℱ` and
`ℱ ⊗^L_𝒪 B̲` are one and the same object of `D(Mod(B̲))` and the two readings of the statement
coincide. The comparison itself is `Stacks.ChaoticSite.derivedColimitTensorComparison`: derived
lower shriek applied to the unit of the derived change-of-coefficients adjunction, followed by
the identification of `Lπ_!` on `B̲`-modules with `Lπ_!` on their underlying `𝒪`-modules, which
is an isomorphism because restriction of scalars does not change the underlying abelian
presheaf.

Both hypotheses of [Stacks, Tag 08RX] are discharged, so nothing is assumed:
`CommAlgCat.isPointResolution_standardResolutionSmallCosimplicialObject` is [Stacks, Tag 08PS]
at this model, and
`CommAlgCat.isIso_leftDerivedColimit_map_smallPolynomialAugmentationAbelian` is
`Lπ_!(𝒪) = Lπ_!(B̲)` read degreewise. The dévissage from those two to an arbitrary `𝒪`-module
is `Stacks.ChaoticSite.isIso_derivedColimitTensorComparison_app_single`. -/
@[stacks 08QJ "for an `𝒪`-module in cohomological degree zero, on the small model of the site \
`C_{B/A}`; on a chaotic site `Li^*ℱ` and `ℱ ⊗^L_𝒪 B̲` are the same object"]
public theorem isIso_derivedColimitTensorComparison_smallPolynomialAugmentation
    (F : PresheafOfModules.{u}
      (smallPolynomialStructurePresheaf A B (standardResolutionVarCardinal A B))) :
    IsIso ((Stacks.ChaoticSite.derivedColimitTensorComparison
        (smallPolynomialAugmentation A B (standardResolutionVarCardinal A B))).app
      (DerivedCategory.Q.obj
        ((HomologicalComplex.single (PresheafOfModules.{u}
          (smallPolynomialStructurePresheaf A B (standardResolutionVarCardinal A B)))
            (ComplexShape.up ℤ) 0).obj F))) :=
  Stacks.ChaoticSite.isIso_derivedColimitTensorComparison_app_single
    (standardResolutionSmallCosimplicialObject A B)
    (smallPolynomialAugmentation A B (standardResolutionVarCardinal A B))
    (isPointResolution_standardResolutionSmallCosimplicialObject A B)
    (isIso_leftDerivedColimit_map_smallPolynomialAugmentationAbelian A B) F

end Standard

end CommAlgCat

end
