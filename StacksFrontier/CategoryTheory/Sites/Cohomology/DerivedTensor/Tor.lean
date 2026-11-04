module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BoundedAbove
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatnessAndRightExactness
public import StacksFrontier.Homology.KFlat.BifunctorSingleSecondFactor
import StacksCore.Tactic.StacksAttribute

/-!
# Tor of two modules on a ringed site

Let `(C, O)` be a ringed site and let `F`, `G` be `O`-modules. Their `Tor` modules are

`Tor_p^O(F, G) = H^{-p}(F ⊗_O^{L} G)`,

the cohomology in degree `-p` of the derived tensor product of `F` and `G`, each placed in
degree `0` of `D(O)`.

## Main definitions

* `Stacks.DerivedTensor.RingedSite.torFunctor`: `Tor_p^O(-, -)` as a bifunctor on `O`-modules.
* `Stacks.DerivedTensor.RingedSite.tor`: the `O`-module `Tor_p^O(F, G)`.

## Main results

* `Stacks.DerivedTensor.RingedSite.tor_eq`: the defining formula, spelled out.
* `Stacks.DerivedTensor.RingedSite.isFlat_iff_isZero_tor_one`: **Tag 08FG**, an `O`-module is
  flat if and only if its first `Tor` against every `O`-module vanishes.
* `Stacks.DerivedTensor.RingedSite.isStrictlyLE_single_zero` and
  `Stacks.DerivedTensor.RingedSite.isIso_homologyMap_mapHomologicalComplex_of_isStrictlyLE`:
  two statements about an arbitrary abelian category on which the computation below rests — an
  object placed in degree `0` gives a complex vanishing in positive degrees, and an additive
  functor preserving finite colimits is an isomorphism on the degree-`0` cohomology of a
  quasi-isomorphism between such complexes.

## Implementation notes

The derived tensor product used is the canonical one of Tag 06YU,
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, the bifunctor of
`Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct`; nothing here re-chooses it.
An `O`-module is placed in degree `0` by Mathlib's
`CategoryTheory.DerivedCategory.singleFunctor` and the cohomology is taken by
`CategoryTheory.DerivedCategory.homologyFunctor`, so `Tor` is functorial in both arguments by
construction and `tor` is the value of the bifunctor rather than a separate definition.

Indexing follows the source: `tor R p` is homological indexing, so it is cohomology in degree
`-p`; in particular `Tor_0` is the ordinary tensor product and `Tor_p` vanishes for `p < 0`.

The hypotheses are exactly those under which the derived tensor product on a ringed site is
available: the site is small and its object and hom universes agree with the universe of the
sections of the structure sheaf and of the modules, the additivity and total-complex
hypotheses on `Stacks.SheafOfModules.Tensor.sheafTensor` are carried as instance arguments,
and the derived category's own hom universe stays independent as `HasDerivedCategory.{d}`.
That narrowing is inherited from the existence of K-flat resolutions (Tag 06YS) and is not
introduced here.

The ringed-space case, `Stacks.Cohomology.tor` of Tag 08BP, is this construction at the site
of opens of the space: the derived tensor product it uses is
`Stacks.Cohomology.TorAmplitude.derTensor`, which is
`Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct` of the structure sheaf.

The characterisation of flatness is organised around a single computation of `Tor_1`, carried
out once and used in both directions. If `P` is a K-flat complex with a quasi-isomorphism
`P ⟶ F[0]`, then `Tor_1^O(F, G)` is the degree-`(-1)` cohomology of the termwise tensor product
`p ↦ P^p ⊗_O G` (`Stacks.DerivedTensor.RingedSite.torOneIso`): the left K-flat comparison of
Tag 06YU replaces the derived tensor product by the total tensor complex, and
`CochainComplex.KFlatBifunctor.totalSingleIso` identifies that total complex with the termwise
one, the second factor being concentrated in degree `0`.

Taking `P = F[0]`, which is K-flat by Tag 06YQ when `F` is flat, the termwise complex vanishes
in degree `-1` and the first `Tor` vanishes with it. Taking instead for `P` a flat resolution of
`F` concentrated in nonpositive degrees — Tag 05T7 applied to the flat covers of Tag 03EW,
K-flat again by Tag 06YQ — the terms of `P` are flat, so a short exact sequence of `O`-modules
stays short exact after tensoring termwise by `P`; the long exact cohomology sequence of the
resulting short exact sequence of complexes then turns the vanishing of `Tor_1` into
injectivity of `H^0(P^• ⊗_O G) ⟶ H^0(P^• ⊗_O H)`. The degree-`0` cohomology of `P^• ⊗_O -` is
`F ⊗_O -`, because tensoring is right exact and `P ⟶ F[0]` is a quasi-isomorphism between
complexes vanishing in positive degrees, so `F ⊗_O -` preserves monomorphisms; being right
exact as well, it is exact, which is flatness of `F` read through the symmetry of `⊗_O`.

## References

* [Stacks Project, Tag 08FF](https://stacks.math.columbia.edu/tag/08FF)
* [Stacks Project, Tag 08FG](https://stacks.math.columbia.edu/tag/08FG)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d

namespace Stacks.DerivedTensor.RingedSite

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Modules R)]
variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).obj M).Additive]
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- `Tor_p^O(-, -)` as a bifunctor on `O`-modules: place both arguments in degree `0` of
`D(O)`, take their derived tensor product, and read off cohomology in degree `-p`. -/
def torFunctor (p : ℤ) : Modules R ⥤ Modules R ⥤ Modules R :=
  DerivedCategory.singleFunctor (Modules R) 0 ⋙ derivedTensorProductFunctor R ⋙
    ((Functor.whiskeringLeft (Modules R) (DerivedModules R) (DerivedModules R)).obj
        (DerivedCategory.singleFunctor (Modules R) 0) ⋙
      (Functor.whiskeringRight (Modules R) (DerivedModules R) (Modules R)).obj
        (DerivedCategory.homologyFunctor (Modules R) (-p)))

/-- **The Tor's of two `O`-modules on a ringed site.** The `O`-module
`Tor_p^O(F, G) = H^{-p}(F ⊗_O^{L} G)`. -/
@[stacks 08FF, sga "4 XVII 4.1.8" "modules, not complexes"]
def tor (p : ℤ) (F G : Modules R) : Modules R := ((torFunctor R p).obj F).obj G

/-- The defining formula for `Tor_p^O(F, G)`: cohomology in degree `-p` of the derived tensor
product of `F` and `G`, each placed in degree `0`. -/
theorem tor_eq (p : ℤ) (F G : Modules R) :
    tor R p F G =
      (DerivedCategory.homologyFunctor (Modules R) (-p)).obj
        (((derivedTensorProductFunctor R).obj
            ((DerivedCategory.singleFunctor (Modules R) 0).obj F)).obj
          ((DerivedCategory.singleFunctor (Modules R) 0).obj G)) :=
  rfl

end Stacks.DerivedTensor.RingedSite

/-! ### Resolutions and the degree-zero cohomology of a termwise image

The lemmas of this section are statements about an arbitrary additive right exact functor
between abelian categories and an arbitrary resolution of an object by a complex concentrated in
nonpositive degrees. They are what turns the first `Tor` of a module into the ordinary tensor
product in degree `0`.
-/

namespace Stacks.DerivedTensor.RingedSite

open CategoryTheory.Limits

section Resolution

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]

/-- An object placed in degree `0` gives a complex vanishing in positive degrees. -/
private lemma isStrictlyLE_single (M : A) :
    CochainComplex.IsStrictlyLE
      ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M) 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i (by omega)

/-- An object placed in degree `0` gives a complex vanishing in positive degrees. -/
alias isStrictlyLE_single_zero := isStrictlyLE_single

/-- **A right exact functor computes degree-zero cohomology of a nonpositive resolution.** If
`φ : K ⟶ L` is a quasi-isomorphism of complexes vanishing in positive degrees and `Φ` is an
additive functor preserving finite colimits, then `Φ` applied termwise to `φ` is an isomorphism
on degree-`0` cohomology.

Vanishing in positive degrees makes the degree-`0` short complex of each of `K` and `L` have
zero second map, so `Φ` preserves its left homology; preservation of left homology carries the
degree-`0` quasi-isomorphism across. -/
private lemma isIso_homologyMap_mapHomologicalComplex (Φ : A ⥤ B) [Φ.Additive]
    [PreservesFiniteColimits Φ] {K L : CochainComplex A ℤ} (φ : K ⟶ L) [QuasiIso φ]
    [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] :
    IsIso (HomologicalComplex.homologyMap
      ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) 0) := by
  have hzero : ∀ (M : CochainComplex A ℤ) [M.IsStrictlyLE 0],
      ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) 0).obj M).g = 0 := by
    intro M _
    show M.d 0 ((ComplexShape.up ℤ).next 0) = 0
    exact (CochainComplex.isZero_of_isStrictlyLE M 0 ((ComplexShape.up ℤ).next 0)
      (by rw [CochainComplex.next]; omega)).eq_of_tgt _ _
  have hΦ : ∀ (M : CochainComplex A ℤ) [M.IsStrictlyLE 0], Φ.PreservesLeftHomologyOf
      ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) 0).obj M) :=
    fun M _ => Functor.preservesLeftHomology_of_zero_g Φ _ (hzero M)
  have := hΦ K
  have := hΦ L
  have hq : ShortComplex.QuasiIso
      ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) 0).map φ) :=
    (quasiIsoAt_iff φ 0).mp inferInstance
  rw [← quasiIsoAt_iff_isIso_homologyMap, quasiIsoAt_iff]
  exact ShortComplex.quasiIso_map_of_preservesLeftHomology Φ
    ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) 0).map φ)

/-- **A right exact functor computes degree-zero cohomology of a nonpositive resolution.** If
`φ : K ⟶ L` is a quasi-isomorphism of complexes vanishing in positive degrees and `Φ` is an
additive functor preserving finite colimits, then `Φ` applied termwise to `φ` is an isomorphism
on degree-`0` cohomology.

Vanishing in positive degrees makes the degree-`0` short complex of each of `K` and `L` have
zero second map, so `Φ` preserves its left homology; preservation of left homology carries the
degree-`0` quasi-isomorphism across. -/
alias isIso_homologyMap_mapHomologicalComplex_of_isStrictlyLE := isIso_homologyMap_mapHomologicalComplex

/-- The comparison `Φ(M[0]) ≅ (Φ M)[0]` of `HomologicalComplex.singleMapHomologicalComplex` is
natural in the functor `Φ`. Both sides are the identity of `Φ M` in degree `0`, up to the
identifications of the degree-`0` terms, and the target vanishes elsewhere. -/
private lemma singleMapHomologicalComplex_app_naturality {Φ Ψ : A ⥤ B}
    [Φ.PreservesZeroMorphisms] [Ψ.PreservesZeroMorphisms] (τ : Φ ⟶ Ψ) (M : A) :
    (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M) ≫
      ((HomologicalComplex.singleMapHomologicalComplex Ψ (ComplexShape.up ℤ) 0).app M).hom =
    ((HomologicalComplex.singleMapHomologicalComplex Φ (ComplexShape.up ℤ) 0).app M).hom ≫
      (HomologicalComplex.single B (ComplexShape.up ℤ) 0).map (τ.app M) := by
  have h0 : ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M).X 0 = M := by simp
  have key := (τ.naturality (eqToHom h0)).symm
  rw [eqToHom_map, eqToHom_map] at key
  ext i
  dsimp [HomologicalComplex.singleMapHomologicalComplex]
  split_ifs with h
  · subst h
    simp only [HomologicalComplex.single_map_f_self, HomologicalComplex.singleObjXSelf,
      HomologicalComplex.singleObjXIsoOfEq, eqToIso.hom, eqToIso.inv,
      NatTrans.mapHomologicalComplex_app_f]
    simp only [← Category.assoc, eqToHom_trans]
    rw [← key, Category.assoc, eqToHom_trans]
  · apply (HomologicalComplex.isZero_single_obj_X _ _ _ _ h).eq_of_tgt

/-- **Injectivity on a nonpositive resolution descends to the object resolved.** Let `τ : Φ ⟶ Ψ`
be a morphism of additive right exact functors, let `M` be an object and let `p : P ⟶ M[0]` be a
quasi-isomorphism from a complex vanishing in positive degrees. If `τ` applied termwise to `P`
is injective on degree-`0` cohomology, then `τ` is injective at `M`.

Both `Φ` and `Ψ` compute the degree-`0` cohomology of `P` as their value at `M`, by
`isIso_homologyMap_mapHomologicalComplex`, and the two identifications are compatible with `τ`
by `singleMapHomologicalComplex_app_naturality` and the naturality of
`HomologicalComplex.singleObjHomologySelfIso`. -/
private lemma mono_app_of_mono_homologyMap {Φ Ψ : A ⥤ B} [Φ.Additive] [Ψ.Additive]
    [PreservesFiniteColimits Φ] [PreservesFiniteColimits Ψ] (τ : Φ ⟶ Ψ)
    {M : A} {P : CochainComplex A ℤ}
    (p : P ⟶ (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M)
    [P.IsStrictlyLE 0] [QuasiIso p]
    (h : Mono (HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app P) 0)) :
    Mono (τ.app M) := by
  have := h
  have := isStrictlyLE_single M
  have := isIso_homologyMap_mapHomologicalComplex Φ p
  have := isIso_homologyMap_mapHomologicalComplex Ψ p
  have key : ∀ {X Y Z W : B} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ W) (d : W ⟶ Z) [IsIso a]
      [IsIso d], a ≫ b = c ≫ d → Mono c → Mono b := fun a b c d _ _ e hc => by
    have : Mono (a ≫ b) := e ▸ mono_comp c d
    exact (mono_comp_iff_of_isIso a b).mp this
  have he : ∀ (Θ : A ⥤ B) [Θ.PreservesZeroMorphisms], IsIso (HomologicalComplex.homologyMap
      ((HomologicalComplex.singleMapHomologicalComplex Θ (ComplexShape.up ℤ) 0).app M).hom 0) :=
    fun Θ _ => (HomologicalComplex.homologyMapIso
      ((HomologicalComplex.singleMapHomologicalComplex Θ (ComplexShape.up ℤ) 0).app M) 0).isIso_hom
  have h₁ : Mono (HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M)) 0) := by
    refine key (HomologicalComplex.homologyMap ((Φ.mapHomologicalComplex _).map p) 0) _ _
      (HomologicalComplex.homologyMap ((Ψ.mapHomologicalComplex _).map p) 0) ?_ h
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      NatTrans.mapHomologicalComplex_naturality τ p]
  have h₂ : Mono (HomologicalComplex.homologyMap
      ((HomologicalComplex.single B (ComplexShape.up ℤ) 0).map (τ.app M)) 0) := by
    refine @key _ _ _ _ _ _ _ _ (he Φ) (he Ψ) ?_ h₁
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      singleMapHomologicalComplex_app_naturality]
  refine key (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (Φ.obj M)).hom _ _
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (Ψ.obj M)).hom ?_ h₂
  exact (HomologicalComplex.singleObjHomologySelfIso_hom_naturality
    (ComplexShape.up ℤ) 0 (τ.app M)).symm

/-- **A right exact functor preserving monomorphisms is exact.** Preserving monomorphisms and
cokernels gives preservation of homology, hence of kernels, hence of all finite limits. -/
private lemma exactFunctor_of_mono_map (Φ : A ⥤ A) [Φ.Additive] [PreservesFiniteColimits Φ]
    (hmono : ∀ {M N : A} (f : M ⟶ N), Mono f → Mono (Φ.map f)) : exactFunctor A A Φ := by
  have : Φ.PreservesMonomorphisms := Functor.PreservesMonomorphisms.mk fun f _ => hmono f ‹_›
  have : Φ.PreservesHomology := Functor.preservesHomology_of_preservesMonos_and_cokernels Φ
  have : ∀ {M N : A} (f : M ⟶ N), PreservesLimit (parallelPair f 0) Φ := fun f =>
    Functor.PreservesHomology.preservesKernel _ f
  rw [exactFunctor_iff]
  exact ⟨Functor.preservesFiniteLimits_of_preservesKernels _, inferInstance⟩

end Resolution

/-! ### Flatness and the vanishing of the first `Tor` -/

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).obj M).Additive]

/-- Tensoring a fixed complex `P` of `O`-modules termwise by a varying `O`-module: the functor
`G ↦ (p ↦ P^p ⊗_O G)`. -/
private def tensorTermwise (P : CochainComplex (Modules R) ℤ) :
    Modules R ⥤ CochainComplex (Modules R) ℤ where
  obj G := (((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj G).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj P
  map f := (NatTrans.mapHomologicalComplex
    ((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.map f) (ComplexShape.up ℤ)).app P

omit [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u} R).obj M).Additive] in
/-- In each degree, `tensorTermwise` is tensoring with the corresponding term of `P`. -/
private lemma tensorTermwise_comp_eval (P : CochainComplex (Modules R) ℤ) (i : ℤ) :
    tensorTermwise R P ⋙ HomologicalComplex.eval (Modules R) (ComplexShape.up ℤ) i =
      (Stacks.SheafOfModules.Tensor.sheafTensor R).obj (P.X i) :=
  rfl

variable
  [∀ (K L : CochainComplex (Modules R) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- Tensoring termwise by a fixed complex preserves zero morphisms, the tensor product being
additive in each variable. -/
private instance preservesZeroMorphisms_tensorTermwise (P : CochainComplex (Modules R) ℤ) :
    (tensorTermwise R P).PreservesZeroMorphisms where
  map_zero X Y := by
    change (NatTrans.mapHomologicalComplex
        ((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.map (0 : X ⟶ Y))
        (ComplexShape.up ℤ)).app P = 0
    rw [Functor.map_zero]
    ext i
    simp

/-- A complex of flat `O`-modules vanishing in positive degrees is K-flat, by Tag 06YQ. -/
private lemma kFlat_of_isStrictlyLE_of_isFlat (P : CochainComplex (Modules R) ℤ)
    (hLE : P.IsStrictlyLE 0)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) (P.X i)) :
    Stacks.SheafOfModules.KFlat.KFlat R P :=
  Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat.{u, u, u} R P ⟨0, hLE⟩ hflat

/-- A flat `O`-module placed in degree `0` gives a K-flat complex, by Tag 06YQ. -/
private lemma kFlat_single_of_isFlat {F : Modules R}
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) F) :
    Stacks.SheafOfModules.KFlat.KFlat R
      ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).obj F) := by
  refine kFlat_of_isStrictlyLE_of_isFlat R _ (isStrictlyLE_single F) fun i => ?_
  by_cases hi : i = 0
  · subst hi
    exact AlgebraicGeometry.SheafOfModules.IsFlat.of_iso R
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).symm hF
  · exact AlgebraicGeometry.SheafOfModules.IsFlat.of_isZero R
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F i hi)

variable [HasDerivedCategory.{d} (Modules R)]

/-- **`Tor_1` computed from a K-flat resolution.** If `P` is a K-flat complex of `O`-modules
with a quasi-isomorphism `q : P ⟶ F[0]`, then `Tor_1^O(F, G)` is the degree-`(-1)` cohomology of
the termwise tensor product `p ↦ P^p ⊗_O G`.

The derived tensor product of `F[0]` with `G[0]` is that of `P` with `G[0]`, since `q` becomes
invertible in `D(O)`; a K-flat left factor computes it as the total tensor complex, by Tag
06YU; and a second factor concentrated in degree `0` makes that total complex the termwise
one. -/
private noncomputable def torOneIso (F G : Modules R) (P : CochainComplex (Modules R) ℤ)
    (hP : Stacks.SheafOfModules.KFlat.KFlat R P)
    (q : P ⟶ (HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).obj F)
    [QuasiIso q] :
    tor R 1 F G ≅ ((tensorTermwise R P).obj G).homology (-1) := by
  have hq : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 inferInstance
  refine (DerivedCategory.homologyFunctor (Modules R) (-1)).mapIso
      (((canonicalDerivedTensorProduct R).tensor.mapIso
        (asIso (DerivedCategory.Q.map q))).app (DerivedCategory.Q.obj
          ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).obj G))).symm ≪≫
    (DerivedCategory.homologyFunctor (Modules R) (-1)).mapIso
      ((canonicalDerivedTensorProduct R).comparisonLeft P _ hP) ≪≫
    (DerivedCategory.homologyFunctorFactors (Modules R) (-1)).app _ ≪≫
    (HomologicalComplex.homologyFunctor (Modules R) (ComplexShape.up ℤ) (-1)).mapIso ?_
  exact CochainComplex.KFlatBifunctor.totalSingleIso
    (Stacks.SheafOfModules.Tensor.sheafTensor R) P G

/-- **Stacks Project, Tag 08FG.** Let `(C, O)` be a ringed site and let `F` be an `O`-module.
Then `F` is a flat `O`-module if and only if `Tor_1^O(F, G) = 0` for every `O`-module `G`. -/
@[stacks 08FG]
theorem isFlat_iff_isZero_tor_one (F : Modules R) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) F ↔
      ∀ G : Modules R, IsZero (tor R 1 F G) := by
  refine ⟨fun hF G => ?_, fun hTor => ?_⟩
  · have h0 := ((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj G).map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F (-1) (by omega))
    have hX : IsZero (((tensorTermwise R
        ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).obj F)).obj G).X (-1)) :=
      h0
    exact (ShortComplex.isZero_homology_of_isZero_X₂ _ hX).of_iso
      (torOneIso R F G _ (kFlat_single_of_isFlat R hF) (𝟙 _))
  · have hF₀ := isStrictlyLE_single (A := Modules R) F
    obtain ⟨P, p, -, hp, hflat, hLE⟩ :=
      (CochainComplex.exists_quasiIso_prop (flatModules R)
        (fun M => by
          obtain ⟨N, π, hN, hπ⟩ :=
            Stacks.SheafOfModules.FlatTensorShortExact.exists_epi_from_flat R M
          exact ⟨N, hN, π, hπ⟩) 0).1
        ((HomologicalComplex.single (Modules R) (ComplexShape.up ℤ) 0).obj F)
    have := hp
    have := hLE
    have hPk := kFlat_of_isStrictlyLE_of_isFlat R P hLE hflat
    have hexact : ∀ i : ℤ,
        exactFunctor (Modules R) (Modules R)
          ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj (P.X i)) := fun i =>
      Stacks.SheafOfModules.exact_sheafTensorObj_of_isFlat.{u, u, u} R (hflat i)
    have hmono : ∀ {M N : Modules R} (f : M ⟶ N), Mono f →
        Mono (((Stacks.SheafOfModules.Tensor.sheafTensor R).obj F).map f) := by
      intro M N f hf
      have := hf
      have := Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorFlipObj R M
      have := Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorFlipObj R N
      have hS : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
        ⟨ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)⟩
      have hSc : ((ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).map
          (tensorTermwise R P)).ShortExact := by
        refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun i => ?_
        rw [← ShortComplex.map_comp]
        have hE := (exactFunctor_iff _).1 (hexact i)
        have : PreservesFiniteLimits (tensorTermwise R P ⋙
            HomologicalComplex.eval (Modules R) (ComplexShape.up ℤ) i) := by
          rw [tensorTermwise_comp_eval]
          exact hE.1
        have : PreservesFiniteColimits (tensorTermwise R P ⋙
            HomologicalComplex.eval (Modules R) (ComplexShape.up ℤ) i) := by
          rw [tensorTermwise_comp_eval]
          exact hE.2
        exact hS.map_of_exact _
      have hz : IsZero (((tensorTermwise R P).obj (cokernel f)).homology (-1)) :=
        (hTor (cokernel f)).of_iso (torOneIso R F (cokernel f) P hPk p).symm
      have hmonoH : Mono (HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex
            ((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.map f)
            (ComplexShape.up ℤ)).app P) 0) :=
        (hSc.homology_exact₁ (-1) 0 (by simp)).mono_g (hz.eq_of_src _ _)
      have hfin : Mono (((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.map f).app F) :=
        mono_app_of_mono_homologyMap _ p hmonoH
      exact hfin
    have := Stacks.SheafOfModules.preservesColimits_sheafTensorObj R F
    have : PreservesFiniteColimits ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj F) :=
      PreservesColimitsOfSize.preservesFiniteColimits _
    exact (Stacks.SheafOfModules.FlatCoproduct.isFlat_iff_exactFunctor_sheafTensor.{u, u} R F).2
      ((exactFunctor _ _).prop_of_iso
        ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding R).app F)
        (exactFunctor_of_mono_map _ hmono))

end Stacks.DerivedTensor.RingedSite

end
