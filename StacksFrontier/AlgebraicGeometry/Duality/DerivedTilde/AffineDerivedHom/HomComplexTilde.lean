module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.AlgebraicGeometry.InternalHomTilde.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.AffineInternalHom
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.CategoryTheory.IsoNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexComparisonNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomFiniteFree
public import StacksFrontier.Homology.HomComplex.ProjectiveRHom
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeExact
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom
public import StacksFrontier.AlgebraicGeometry.ModuleSpecGammaAdditive
import StacksCore.Tactic.StacksAttribute

/-!
# The complex-level affine Hom comparison

Let `R` be a commutative ring and `X = Spec R`. This file builds the complex-level substrate of
clause (3)(b) of [Stacks, Tag 0A6H]: for `P` a bounded complex of finite projective `R`-modules
and `L` an arbitrary complex of `R`-modules, the comparison

`SheafHom^•(P̃, L̃)  ≅  (Hom^•_R(P, L))~`

of complexes of `𝒪_X`-modules. It is the totalisation of the degreewise affine comparison
`SheafHom(M̃, Ñ) ≅ Hom_R(M, N)~` of [Stacks, Tag 01I8]. The derived statement built on it is in
`StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDerivedHom.PerfectSource`, and the
hypothesis-free comparison in
`StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDerivedHom.Comparison`.

## Main definitions

* `AlgebraicGeometry.affineHomComplexTildeIso`: the complex-level comparison
  `SheafHom^•(P̃, L̃) ≅ (Hom^•_R(P, L))~` for `P` a bounded complex of finite projective
  modules. This is the substrate of the clause, and is shared with clause (3)(a).

## Main results

* `AlgebraicGeometry.affineHomComplexTildeIso_inv_toOpen` normalizes the complex-level
  comparison by its action on the canonical global section attached to a Hom cochain; this is
  what singles it out among isomorphisms of those two complexes, excluding in particular a
  global sign.

## Implementation notes

**One category for the sheaf side.** `AlgebraicGeometry.tilde.functor` lands in
`AlgebraicGeometry.Scheme.Modules`, whereas the internal Hom complex, its degreewise projections
and the 08JH comparison are stated for `SheafOfModules X.ringSheaf` over a ringed site `X`. For
`X = AlgebraicGeometry.specSite R` those two are the *same* category with the *same* instances —
`(specSite R).ringSheaf` reduces to `(Spec R).ringCatSheaf` — so everything below is written in
the `Scheme.Modules` spelling and the site-level declarations accept it. Retyping sheafification
into the site spelling, as `AffineDerivedTensor.lean` of this directory does for the tensor
product, would be *wrong* here: it defeats instance synthesis, because `Functor.Additive` and
`Functor.PreservesZeroMorphisms` for the retyped functor are not found from the instances
registered for `tilde.functor` itself.

**Site level throughout.** The space-level internal Hom complex
`Stacks.SheafOfModules.sheafHomComplex` is obtained from the site-level
`AlgebraicGeometry.RingedSite.sheafHomComplex` by `Stacks.SheafOfModules.ofSite`, which copies
`obj` and `sectionsIso` unchanged. Everything below is therefore written at the site level,
where `AlgebraicGeometry.RingedSite.homDegreeProjection`,
`AlgebraicGeometry.RingedSite.sectionsIso_homMap_v` and
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison` all live.

**The sections argument.** The degreewise isomorphism alone does not give an isomorphism of
complexes, because its construction passes through a choice of finite support in each degree.
What upgrades it is that every term of `SheafHom^•(P̃, L̃)` is the sheafification of its module
of global sections — proved from the degreewise isomorphism — so that the whole complex is the
sheafification of its complex of global sections, and that complex is identified with
`Hom^•_R(P, L)` by full faithfulness of sheafification followed by restriction to `⊤`. The
differential is then automatic: `sectionsIso` is an isomorphism of *complexes*, so the
Hom-complex differential `δ` is carried across by
`AlgebraicGeometry.RingedSite.SheafHomComplex.sectionsEquiv_d`.

**The substrate of the clause is hypothesis-free.** `affineHomSectionsComplexIso` identifies
the complex of global sections of `SheafHom^•(P̃, L̃)` with `Hom^•_R(P, L)` for *arbitrary* `P`
and `L`; full faithfulness of sheafification is all it uses. Finiteness and projectivity of the
terms of `P` enter only through `isIso_fromTildeΓ_sheafHomComplex`, the statement that each term
of the internal Hom complex is the sheafification of its global sections.

## References

* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.RingedSite Stacks.SheafOfModules

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
  AlgebraicGeometry.tilde.preservesFiniteLimits
  Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

/-! ### One category for the sheaf side -/

/-- The ringed site of `Spec R`: the site of its opens with the open-cover topology and its
structure sheaf. -/
public abbrev specSite (R : CommRingCat.{u}) : RingedSite.{u, u, u} :=
  Stacks.SheafOfModules.ringedSite (Spec R).sheaf

/-- The complex of `𝒪_{Spec R}`-modules associated degreewise to a complex of `R`-modules. -/
public abbrev tildeCx (R : CommRingCat.{u}) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤
      CochainComplex ((Spec R).Modules) ℤ :=
  (tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Sheafification followed by restriction to the largest open of `Spec R`. It is fully
faithful and additive, so module Hom cochains are the same thing as sheaf Hom cochains over the
whole space. -/
public abbrev tildeTop (R : CommRingCat.{u}) :=
  tilde.functor R ⋙ SheafOfModules.overFunctor
    (structureSheaf (Spec.structureSheaf R)) (⊤ : Opens (PrimeSpectrum.Top R))

public instance tildeTop_additive (R : CommRingCat.{u}) : (tildeTop R).Additive :=
  ⟨by intros; exact tildeOverTop_map_add R _ _⟩

/-! ### The degreewise affine comparison -/

/-- The internal Hom sheaf of two associated sheaves, packaged as an internal hom in
the axiomatic sense of [Stacks, Tag 01CO]. Its sections over `U` are *by definition* the
morphisms of the restrictions to the slice site over `U`, so all three fields hold by `rfl`. -/
public def affineInternalHomSheafPackage (R : CommRingCat.{u}) (M N : ModuleCat.{u} R) :
    SheafHom (Spec.structureSheaf R) (tilde M) (tilde N) where
  obj := internalHomSheaf (specSite R) ((tilde.functor R).obj M) ((tilde.functor R).obj N)
  sectionsEquiv U :=
    { toFun := fun s => ⟨s⟩
      invFun := fun f => f.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  restrict_natural := by intros; rfl
  smul_natural := by intros; rfl

/-- **[Stacks, Tag 01I8] degreewise.** For `M` finitely presented, the internal Hom sheaf of
the associated sheaves of `M` and `N` is the sheaf associated to `Hom_R(M, N)`. -/
public def affineInternalHomTildeIso (R : CommRingCat.{u}) (M N : ModuleCat.{u} R)
    [Module.FinitePresentation R M] :
    internalHomSheaf (specSite R) ((tilde.functor R).obj M) ((tilde.functor R).obj N) ≅
      (tilde.functor R).obj (ModuleCat.of R (M ⟶ N)) :=
  (internalHomTildeIso R M N (affineInternalHomSheafPackage R M N)).iso

/-- A product indexed by a type on which all but finitely many factors vanish agrees with the
coproduct over the same index. -/
private def productCoproductIsoOfFiniteSupport
    {C : Type*} [Category C] [Preadditive C] {ι : Type*}
    (A : ι → C) [HasProduct A] [HasCoproduct A]
    (s : Finset ι) (hs : ∀ i, i ∉ s → IsZero (A i)) : (∏ᶜ A) ≅ ∐ A := by
  classical
  let f : (∏ᶜ A) ⟶ ∐ A := ∑ i ∈ s, Pi.π A i ≫ Sigma.ι A i
  let g : (∐ A) ⟶ ∏ᶜ A := Sigma.desc (fun i => Pi.lift
    (fun j => if h : i = j then eqToHom (congrArg A h) else 0))
  have hg (i j : ι) : Sigma.ι A i ≫ g ≫ Pi.π A j =
      if h : i = j then eqToHom (congrArg A h) else 0 := by simp [g]
  refine ⟨f, g, ?_, ?_⟩
  · apply Pi.hom_ext
    intro j
    by_cases hj : j ∈ s
    · simp only [f, Preadditive.sum_comp, Category.assoc, hg, Category.id_comp]
      rw [Finset.sum_eq_single j]
      · simp
      · intro i hi hij
        simp [hij]
      · simp [hj]
    · exact (hs j hj).eq_of_tgt _ _
  · apply Sigma.hom_ext
    intro i
    by_cases hi : i ∈ s
    · simp only [f, g, Preadditive.comp_sum, Sigma.ι_comp_desc_assoc,
        Pi.lift_comp_π_assoc, Category.comp_id]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j hj hji
        simp [Ne.symm hji]
      · simp [hi]
    · exact (hs i hi).eq_of_src _ _

/-- A degree-`n` Hom cochain is the same thing as a family, indexed by `q : ℤ`, of module maps
`P^{-q} ⟶ L^{n - q}`, `R`-linearly. -/
public def cochainFamilyLinearEquiv {R : Type u} [CommRing R]
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    CochainComplex.HomComplex.Cochain P L n ≃ₗ[R]
      ((q : ℤ) → (P.X (-q) ⟶ L.X (n - q))) := by
  let e : ℤ ≃ CochainComplex.HomComplex.Triplet n :=
    { toFun := fun q => ⟨-q, n - q, by omega⟩
      invFun := fun t => -t.p
      left_inv := fun q => neg_neg q
      right_inv := by
        rintro ⟨p, q, hpq⟩
        dsimp
        congr 1 <;> omega }
  exact (LinearEquiv.piCongrLeft R
    (fun t : CochainComplex.HomComplex.Triplet n => P.X t.p ⟶ L.X t.q) e).symm

/-- Sheafification preserves `ℤ`-indexed coproducts, being a left adjoint. -/
private def affineTildeCoproductIso (R : CommRingCat.{u}) (A : ℤ → ModuleCat.{u} R) :
    (∐ fun q => (tilde.functor R).obj (A q)) ≅ (tilde.functor R).obj (∐ A) :=
  (HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete A (tilde.functor R))).symm ≪≫
    (preservesColimitIso (tilde.functor R) (Discrete.functor A)).symm

/-- The terms of a complex vanish wherever the terms of its sheafification do. -/
private lemma tildeC_support_subset (R : CommRingCat.{u})
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    {i : ℤ | ¬ IsZero (((tildeCx R).obj P).X i)} ⊆ {i : ℤ | ¬ IsZero (P.X i)} :=
  fun _ hi hzero => hi ((tilde.functor R).map_isZero hzero)

/-- **[Stacks, Tag 08JH] and [Stacks, Tag 01I8] combined, degreewise.** For `P` a bounded
complex of finite projective modules, the `n`-th term of the internal Hom complex of `P̃` into
`L̃` is the sheaf associated to the `n`-th term of the module Hom complex of `P` into `L`. -/
private def affineHomDegreeTildeIso (R : CommRingCat.{u})
    (P L : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ i, Projective (P.X i)] [∀ i, Module.Finite R (P.X i)]
    (hP : {i : ℤ | ¬ IsZero (P.X i)}.Finite) (n : ℤ) :
    (sheafHomComplex (specSite R) ((tildeCx R).obj P) ((tildeCx R).obj L)).obj.X n ≅
      (tilde.functor R).obj ((CochainComplex.HomComplexR R P L).X n) := by
  classical
  let E := (tildeCx R).obj P
  let F := (tildeCx R).obj L
  let A : ℤ → ModuleCat.{u} R := fun q => ModuleCat.of R (P.X (-q) ⟶ L.X (n - q))
  let s := hP.toFinset.image (fun i : ℤ => -i)
  have hs : ∀ q, q ∉ s → IsZero (A q) := by
    intro q hq
    have hPzero : IsZero (P.X (-q)) := by
      by_contra hzero
      exact hq (Finset.mem_image.mpr ⟨-q, hP.mem_toFinset.mpr hzero, neg_neg q⟩)
    have : Subsingleton (P.X (-q) ⟶ L.X (n - q)) :=
      Subsingleton.intro fun f g => hPzero.eq_of_src _ _
    exact ModuleCat.isZero_of_subsingleton _
  have hterms : ∀ q : ℤ,
      internalHomSheaf (specSite R) (E.X (-q)) (F.X (n - q)) ≅ (tilde.functor R).obj (A q) := by
    intro q
    letI : Module.FinitePresentation R (P.X (-q)) :=
      Module.finitePresentation_of_projective R (P.X (-q))
    exact affineInternalHomTildeIso R (P.X (-q)) (L.X (n - q))
  let eA : ModuleCat.of R (∀ q : ℤ, P.X (-q) ⟶ L.X (n - q)) ≅ ∐ A :=
    (ModuleCat.piIsoPi A).symm ≪≫ productCoproductIsoOfFiniteSupport A s hs
  exact (strictlyPerfectHomDegreeIso (specSite R) E F
      (hP.subset (tildeC_support_subset R P)) n).trans
    ((Sigma.mapIso hterms).trans
      ((affineTildeCoproductIso R A) ≪≫
        (tilde.functor R).mapIso eA.symm ≪≫
        (tilde.functor R).mapIso (cochainFamilyLinearEquiv P L n).toModuleIso.symm))

/-! ### The sections argument -/

/-- Along a fully faithful additive functor, Hom cochains of two complexes are the Hom cochains
of the two image complexes. -/
def fullyFaithfulCochainAddEquiv {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (T : C ⥤ D) [T.Additive] (hT : T.FullyFaithful)
    (P L : CochainComplex C ℤ) (n : ℤ) :
    CochainComplex.HomComplex.Cochain P L n ≃+
      CochainComplex.HomComplex.Cochain
        ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
        ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) n where
  toFun z := z.map T
  invFun z := CochainComplex.HomComplex.Cochain.mk fun p q h => hT.preimage (z.v p q h)
  left_inv z := by
    ext p q h
    exact hT.preimage_map _
  right_inv z := by
    ext p q h
    exact hT.map_preimage _
  map_add' z w := CochainComplex.HomComplex.Cochain.map_add z w T

/-- The module Hom cochain attached to a global section of the internal Hom complex: its
`(-q, n - q)` component is the `q`-th degreewise projection of the section, read as a module map
through [Stacks, Tag 01I8] at the level of global sections. -/
public def affineHomSectionsLinearMap (R : CommRingCat.{u})
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (moduleSpecΓFunctor (R := R)).obj
      ((sheafHomComplex (specSite R) ((tildeCx R).obj P) ((tildeCx R).obj L)).obj.X n) →ₗ[R]
      CochainComplex.HomComplex.Cochain P L n :=
  (cochainFamilyLinearEquiv P L n).symm.toLinearMap.comp
    (LinearMap.pi fun q =>
      (sheafHomTildeΓLinearEquiv R (P.X (-q)) (L.X (n - q))
        (affineInternalHomSheafPackage R (P.X (-q)) (L.X (n - q)))).toLinearMap.comp
          ((moduleSpecΓFunctor (R := R)).map (homDegreeProjection (specSite R)
            ((tildeCx R).obj P) ((tildeCx R).obj L) n q)).hom)

/-- The components of `affineHomSectionsLinearMap`: they are the components of the section,
read as a sheaf Hom cochain over the whole space, pulled back along `tildeTop`. -/
public lemma affineHomSectionsLinearMap_v (R : CommRingCat.{u})
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (n p q : ℤ) (hpq : p + n = q)
    (s : (moduleSpecΓFunctor (R := R)).obj
      ((sheafHomComplex (specSite R) ((tildeCx R).obj P) ((tildeCx R).obj L)).obj.X n)) :
    (affineHomSectionsLinearMap R P L n s).v p q hpq =
      (fullyFaithfulTildeOverTop R).preimage
        (((sheafHomComplex (specSite R) ((tildeCx R).obj P) ((tildeCx R).obj L)).sectionsEquiv
          ⊤ n s).v p q hpq) := by
  have hv (t : ℤ) : (affineHomSectionsLinearMap R P L n s).v (-t) (n - t) (by omega) =
      (fullyFaithfulTildeOverTop R).preimage
        (((sheafHomComplex (specSite R) ((tildeCx R).obj P)
          ((tildeCx R).obj L)).sectionsEquiv ⊤ n s).v (-t) (n - t) (by omega)) :=
    congrFun ((cochainFamilyLinearEquiv P L n).apply_symm_apply _) t
  obtain ⟨t, rfl⟩ : ∃ t : ℤ, p = -t := ⟨-p, by omega⟩
  obtain rfl : q = n - t := by omega
  exact hv t

/-- Mapping the module Hom cochain attached to a section forward along `tildeTop` recovers the
section itself, read as a sheaf Hom cochain over the whole space. -/
public lemma affineHomSectionsLinearMap_map (R : CommRingCat.{u})
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (s : (moduleSpecΓFunctor (R := R)).obj
      ((sheafHomComplex (specSite R) ((tildeCx R).obj P) ((tildeCx R).obj L)).obj.X n)) :
    (affineHomSectionsLinearMap R P L n s).map (tildeTop R) =
      (sheafHomComplex (specSite R) ((tildeCx R).obj P)
        ((tildeCx R).obj L)).sectionsEquiv ⊤ n s := by
  ext p q hpq : 1
  rw [CochainComplex.HomComplex.Cochain.map_v, affineHomSectionsLinearMap_v]
  exact (fullyFaithfulTildeOverTop R).map_preimage _

/-- `affineHomSectionsLinearMap` is bijective: it is full faithfulness of `tildeTop`
conjugated by the identification of sections of the internal Hom complex with Hom cochains. -/
public def affineHomSectionsLinearEquiv (R : CommRingCat.{u})
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (moduleSpecΓFunctor (R := R)).obj
      ((sheafHomComplex (specSite R) ((tildeCx R).obj P) ((tildeCx R).obj L)).obj.X n) ≃ₗ[R]
      CochainComplex.HomComplex.Cochain P L n := by
  let e := (sheafHomComplex (specSite R) ((tildeCx R).obj P)
    ((tildeCx R).obj L)).sectionsEquiv ⊤ n
  let e' := fullyFaithfulCochainAddEquiv (tildeTop R) (fullyFaithfulTildeOverTop R) P L n
  apply LinearEquiv.ofBijective (affineHomSectionsLinearMap R P L n)
  have he : (affineHomSectionsLinearMap R P L n : _ → _) = fun s => e'.symm (e s) := by
    funext s
    apply e'.injective
    exact (affineHomSectionsLinearMap_map R P L n s).trans (e'.apply_symm_apply (e s)).symm
  rw [he]
  exact e'.symm.bijective.comp e.bijective

/-- Each term of the internal Hom complex of two sheafified complexes is itself the
sheafification of its module of global sections. -/
private lemma isIso_fromTildeΓ_sheafHomComplex (R : CommRingCat.{u})
    (P L : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ i, Projective (P.X i)] [∀ i, Module.Finite R (P.X i)]
    (hP : {i : ℤ | ¬ IsZero (P.X i)}.Finite) (n : ℤ) :
    IsIso (Scheme.Modules.fromTildeΓ
      ((sheafHomComplex (specSite R) ((tildeCx R).obj P) ((tildeCx R).obj L)).obj.X n)) :=
  isIso_fromTildeΓ_iff.mpr
    ⟨(CochainComplex.HomComplexR R P L).X n,
      ⟨(affineHomDegreeTildeIso R P L hP n).symm⟩⟩

/-- The canonical degreewise comparison, the one whose inverse is pinned down by its action on
canonical global sections. -/
private def affineHomCanonicalDegreeIso (R : CommRingCat.{u})
    (P L : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ i, Projective (P.X i)] [∀ i, Module.Finite R (P.X i)]
    (hP : {i : ℤ | ¬ IsZero (P.X i)}.Finite) (n : ℤ) :
    (sheafHomComplex (specSite R) ((tildeCx R).obj P) ((tildeCx R).obj L)).obj.X n ≅
      (tilde.functor R).obj ((CochainComplex.HomComplexR R P L).X n) := by
  have := isIso_fromTildeΓ_sheafHomComplex R P L hP n
  exact (asIso (Scheme.Modules.fromTildeΓ
      ((sheafHomComplex (specSite R) ((tildeCx R).obj P) ((tildeCx R).obj L)).obj.X n))).symm ≪≫
    (tilde.functor R).mapIso (affineHomSectionsLinearEquiv R P L n).toModuleIso

/-- The inverse of the canonical degreewise comparison sends the canonical global section
attached to a Hom cochain `α` to the section whose components are the sheaf maps induced by the
components of `α`. -/
private lemma affineHomCanonicalDegreeIso_inv_sections (R : CommRingCat.{u})
    (P L : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ i, Projective (P.X i)] [∀ i, Module.Finite R (P.X i)]
    (hP : {i : ℤ | ¬ IsZero (P.X i)}.Finite)
    (n p q : ℤ) (hpq : p + n = q) (α : CochainComplex.HomComplex.Cochain P L n) :
    (((sheafHomComplex (specSite R) ((tildeCx R).obj P) ((tildeCx R).obj L)).sectionsEquiv ⊤ n
        (((affineHomCanonicalDegreeIso R P L hP n).inv).val.app (op ⊤)
          (tilde.toOpen ((CochainComplex.HomComplexR R P L).X n) ⊤ α))).v p q hpq) =
      (tilde.map (α.v p q hpq)).over ⊤ := by
  let H := sheafHomComplex (specSite R) ((tildeCx R).obj P) ((tildeCx R).obj L)
  let e := affineHomSectionsLinearEquiv R P L n
  set s := ((affineHomCanonicalDegreeIso R P L hP n).inv).val.app (op ⊤)
    (tilde.toOpen ((CochainComplex.HomComplexR R P L).X n) ⊤ α) with hs
  have hc := congrArg (fun k : (CochainComplex.HomComplexR R P L).X n ⟶
      (moduleSpecΓFunctor (R := R)).obj (H.obj.X n) => k α)
    (tilde_adjunction_unit_map_counit (R := R) (H.obj.X n) e.toModuleIso.inv)
  have he : affineHomSectionsLinearMap R P L n s = α := by
    change e _ = α
    convert e.apply_symm_apply α using 1
    exact congrArg e hc
  have hv : (fullyFaithfulTildeOverTop R).preimage ((H.sectionsEquiv ⊤ n s).v p q hpq) =
      α.v p q hpq :=
    (affineHomSectionsLinearMap_v R P L n p q hpq _).symm.trans
      (congrArg (fun z : CochainComplex.HomComplex.Cochain P L n => z.v p q hpq) he)
  exact ((fullyFaithfulTildeOverTop R).map_preimage _).symm.trans (congrArg (tildeTop R).map hv)

/-- Two morphisms out of a sheafification agree as soon as they agree on the canonical global
sections. -/
public lemma tildeHom_ext_globalSections (R : CommRingCat.{u}) {M : ModuleCat.{u} R}
    {Q : (Spec R).Modules} (f g : tilde M ⟶ Q)
    (h : ∀ x : M, f.val.app (op ⊤) (tilde.toOpen M ⊤ x) =
      g.val.app (op ⊤) (tilde.toOpen M ⊤ x)) : f = g :=
  ((tilde.adjunction (R := R)).homEquiv M Q).injective (ModuleCat.hom_ext (LinearMap.ext h))

/-- The module Hom cochain attached to a section commutes with the differentials. -/
public lemma affineHomSectionsLinearMap_δ (R : CommRingCat.{u})
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (n m : ℤ)
    (s : (moduleSpecΓFunctor (R := R)).obj
      ((sheafHomComplex (specSite R) ((tildeCx R).obj P) ((tildeCx R).obj L)).obj.X n)) :
    CochainComplex.HomComplex.δ n m (affineHomSectionsLinearMap R P L n s) =
      affineHomSectionsLinearMap R P L m
        (((moduleSpecΓFunctor (R := R)).map ((sheafHomComplex (specSite R) ((tildeCx R).obj P)
          ((tildeCx R).obj L)).obj.d n m)).hom s) := by
  let H := sheafHomComplex (specSite R) ((tildeCx R).obj P) ((tildeCx R).obj L)
  apply (fullyFaithfulCochainAddEquiv (tildeTop R)
    (fullyFaithfulTildeOverTop R) P L m).injective
  change (CochainComplex.HomComplex.δ n m
      (affineHomSectionsLinearMap R P L n s)).map (tildeTop R) =
    (affineHomSectionsLinearMap R P L m
      (((moduleSpecΓFunctor (R := R)).map (H.obj.d n m)).hom s)).map (tildeTop R)
  rw [← CochainComplex.HomComplex.δ_map, affineHomSectionsLinearMap_map,
    affineHomSectionsLinearMap_map]
  exact (H.sectionsEquiv_d ⊤ n m s).symm

/-- The degreewise identification of global sections with Hom cochains is a morphism of
complexes. -/
public lemma affineHomSectionsLinearEquiv_comm (R : CommRingCat.{u})
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) (n m : ℤ) :
    (affineHomSectionsLinearEquiv R P L n).toModuleIso.hom ≫
        (CochainComplex.HomComplexR R P L).d n m =
      (((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (sheafHomComplex (specSite R) ((tildeCx R).obj P) ((tildeCx R).obj L)).obj).d n m ≫
        (affineHomSectionsLinearEquiv R P L m).toModuleIso.hom :=
  ModuleCat.hom_ext (LinearMap.ext fun s => affineHomSectionsLinearMap_δ R P L n m s)

/-- The complex of global sections of the internal Hom complex of two sheafified complexes is
the module Hom complex. -/
public def affineHomSectionsComplexIso (R : CommRingCat.{u})
    (P L : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (sheafHomComplex (specSite R) ((tildeCx R).obj P) ((tildeCx R).obj L)).obj ≅
      CochainComplex.HomComplexR R P L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (affineHomSectionsLinearEquiv R P L n).toModuleIso)
    (fun n m _ => affineHomSectionsLinearEquiv_comm R P L n m)

/-- The degreewise counit of the sheafification adjunction, assembled into a morphism from the
sheafification of the complex of global sections. -/
public def fromTildeΓComplex (R : CommRingCat.{u})
    (K : CochainComplex ((Spec R).Modules) ℤ) :
    (tildeCx R).obj
      (((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
      K where
  f n := Scheme.Modules.fromTildeΓ (K.X n)
  comm' n m _ := (Scheme.Modules.fromTildeΓNatTrans.naturality (K.d n m)).symm

/-- A complex of modules on an affine scheme whose terms are all sheafifications of their
global sections is the sheafification of its complex of global sections. -/
public def tildeΓComplexIso (R : CommRingCat.{u})
    (K : CochainComplex ((Spec R).Modules) ℤ)
    (hiso : ∀ n, IsIso (Scheme.Modules.fromTildeΓ (K.X n))) :
    (tildeCx R).obj
      (((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      K := by
  haveI : ∀ n, IsIso ((fromTildeΓComplex R K).f n) := hiso
  haveI := HomologicalComplex.Hom.isIso_of_components (fromTildeΓComplex R K)
  exact asIso (fromTildeΓComplex R K)

/-! ### The complex-level affine comparison -/

/-- **The complex-level affine Hom comparison.** For `P` a bounded complex of finite projective
`R`-modules and `L` an arbitrary complex of `R`-modules, the internal Hom complex of `P̃` into
`L̃` on `Spec R` is the sheafification of the module Hom complex of `P` into `L`.

Its components are the canonical module-Hom to sheaf-Hom comparisons of [Stacks, Tag 01I8],
assembled using the finite support of `P`; this is the substrate of clause (3)(b) of
[Stacks, Tag 0A6H] and is untagged because the clause itself is the derived statement
`affinePerfectDerivedSheafHomIso`. Clause (3)(a) uses it too. -/
@[no_expose]
public def affineHomComplexTildeIso (R : CommRingCat.{u})
    (P L : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ i, Projective (P.X i)] [∀ i, Module.Finite R (P.X i)]
    (hP : {i : ℤ | ¬ IsZero (P.X i)}.Finite) :
    (sheafHomComplex (specSite R) ((tildeCx R).obj P) ((tildeCx R).obj L)).obj ≅
      (tildeCx R).obj (CochainComplex.HomComplexR R P L) :=
  (tildeΓComplexIso R _
      (fun n => isIso_fromTildeΓ_sheafHomComplex R P L hP n)).symm ≪≫
    (tildeCx R).mapIso (affineHomSectionsComplexIso R P L)

/-- **The normalization of `affineHomComplexTildeIso`.** Its inverse takes the canonical global
section attached to a module Hom cochain `α` to the sheaf Hom cochain whose components are the
sheaf maps induced by the components of `α`. In particular this excludes a global sign
ambiguity, and it is what identifies the derived comparison below. -/
public theorem affineHomComplexTildeIso_inv_toOpen (R : CommRingCat.{u})
    (P L : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ i, Projective (P.X i)] [∀ i, Module.Finite R (P.X i)]
    (hP : {i : ℤ | ¬ IsZero (P.X i)}.Finite)
    (n p q : ℤ) (hpq : p + n = q) (α : CochainComplex.HomComplex.Cochain P L n) :
    (((sheafHomComplex (specSite R) ((tildeCx R).obj P) ((tildeCx R).obj L)).sectionsEquiv ⊤ n
        (((affineHomComplexTildeIso R P L hP).inv.f n).val.app (op ⊤)
          (tilde.toOpen ((CochainComplex.HomComplexR R P L).X n) ⊤ α))).v p q hpq) =
      (tilde.map (α.v p q hpq)).over ⊤ :=
  affineHomCanonicalDegreeIso_inv_sections R P L hP n p q hpq α

end AlgebraicGeometry

end
