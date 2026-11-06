module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.HigherVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.SmallEtaleSignTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleHigherPushforwardEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections

/-!
# Higher vanishing for quasi-coherent sheaves on a quasi-compact separated algebraic space

Let `S` be a scheme, `X` a separated algebraic space over `S`, `U` an affine scheme and
`f : U → X` a surjective étale morphism whose base changes to fields have degree at most `d` (the
reading of the source's fibre bound that its proof uses, see the implementation notes).
Then `H^q(X, ℱ) = 0` for every quasi-coherent `𝒪_X`-module `ℱ` and every `q ≥ d`
[Stacks, Tag 072B].

The proof is the alternating Čech complex of the covering `U → X`.  Let `W_p` be the complement
of all the diagonals in the `(p+1)`-fold self-product of `U` over `X`, with its free action of
the symmetric group `S_{p+1}` [Stacks, Tag 0726].  The functors `ℱ ↦ ℱ(W_p)^{sign}` of
anti-invariant sections form, after the global sections, a resolution of the global sections
functor on injective modules — they are the terms `Hom(∧^{p+1} ℤ[h_U], -)` of the Koszul complex
of sections, and `∧^{•+1} ℤ[h_U] ⟶ ℤ` is a resolution by objectwise torsion-free presheaves
[Stacks, Tag 0723] — so they compute the cohomology of every `ℱ` acyclic for all of them
(`Stacks.SheafOfModules.isZero_rightDerived_globalSectionsHom`).  Separatedness of `X` makes
`W_p` an affine scheme, so a quasi-coherent `ℱ` has no higher cohomology on `W_p`
[Stacks, Tag 01XB]; and because `S_{p+1}` acts freely on `W_p`, some function on `W_p` has
trace `1`, which splits the anti-invariant sections off the sections over `W_p` naturally in
`ℱ`.  So `ℱ` is acyclic for every term.  Finally the degree bound empties `W_p` for `p ≥ d`, so
the terms vanish there, and the cohomology of `ℱ` vanishes in degrees `≥ d`.

## Main definitions

* `Stacks.SheafOfModules.globalSectionsHomIso`: global sections of a sheaf of modules are the
  maps to it from the constant presheaf `ℤ`.
* `AlgebraicGeometry.Space.SmallEtale.koszulTermToSections`,
  `AlgebraicGeometry.Space.SmallEtale.sectionsToKoszulTerm`: the inclusion of the anti-invariant
  sections over `W_n` into all the sections, and its retraction `s ↦ ∑_σ sign(σ) σ^*(t s)`.

## Main results

* `Stacks.SheafOfModules.isZero_rightDerived_globalSectionsFunctor_of_koszulSections`: the Koszul
  complex of sections of a covering object computes the cohomology of the modules acyclic for its
  terms, in the vanishing form.
* `AlgebraicGeometry.Space.SmallEtale.isZero_rightDerived_koszulSectionsTerm`: a
  quasi-coherent module is acyclic for every term of the Koszul complex of sections of an affine
  étale chart of a separated algebraic space.
* `AlgebraicGeometry.Space.SmallEtale.isZero_koszulSectionsTerm_obj`: the terms vanish above the
  fibre bound.
* `AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsFunctor_of_isSeparated`:
  **[Stacks, Tag 072B]**.

## Implementation notes

**The source's quotients `U_p = W_p/S_{p+1}` are not formed.** The source computes the first page
of the alternating Čech spectral sequence as the cohomology of the sign twists on the quotients
`U_p`, which are affine by Groupoids, Proposition 39.23.9 of the source. Here the same vanishing is
obtained on `W_p` itself: the anti-invariant sections over `W_p` are a natural direct summand of
all the sections over `W_p`, the projection being `s ↦ ∑_σ sign(σ) σ^*(t s)` for a function `t` of
trace `1`, whose existence is the freeness of the action
(`MulSemiringAction.exists_sum_smul_eq_one`). No spectral sequence is used either: the passage from
the vanishing of the terms to that of the cohomology is dimension shifting
(`Stacks.Cohomology.RightDerivedCoEdge.isZero_rightDerived_of_isZero_X`).

**The fibre bound.**  The source bounds "the size of the fibres of `|U| → |X|`".  Here `d` is
read as a bound on the *degree* of the base changes of `f` to fields, the condition of
[Stacks, Tag 03JL] with explicit constant `d`: this is what the source's proof uses (the emptiness
of `W_p` for `p ≥ d`), and it is the bound that [Stacks, Tag 072C] produces.  The literal reading,
a bound on the number of points of the fibres of `|U| → |X|`, is neither proved nor refuted here.
For it the step `W_p = ∅` of the source's proof fails: for `X = Spec k` and `U = Spec k'` with
`k'/k` separable quadratic, each fibre of `|U| → |X|` has one point, while `f` has degree `2` and
`W_1 = U ×_X U ∖ Δ` is not empty.  The conclusion still holds in that example, since `X` is
affine.

**Quasi-compactness of `X`** is not assumed: it follows from the existence of the surjection
from an affine scheme.  Separatedness is the absolute notion of [Stacks, Tag 03BO].

## References

* [Stacks Project, Tag 072B](https://stacks.math.columbia.edu/tag/072B)
* [Stacks Project, Tag 0728](https://stacks.math.columbia.edu/tag/0728)
* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
* [Stacks Project, Tag 0723](https://stacks.math.columbia.edu/tag/0723)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace Stacks.SheafOfModules

open AddCommGrpCat

variable {C : Type w} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})

/-! ### Comparison with the global sections functor -/

/-- The global section of a module given by a map from the constant presheaf `ℤ`: its values
at `1`. -/
def sectionsOfConstantIntHom (M : SheafOfModules.{u} R)
    (α : constantInt.{u} C ⟶ (underlyingPresheaf R).obj M) : M.sections :=
  ⟨fun X => α.app X (ULift.up 1), fun {_ _} f =>
    (NatTrans.naturality_apply α f (ULift.up 1)).symm⟩

/-- The map from the constant presheaf `ℤ` to a module given by a global section `s`:
`n ↦ n • s`. -/
def constantIntHomOfSections (M : SheafOfModules.{u} R) (s : M.sections) :
    constantInt.{u} C ⟶ (underlyingPresheaf R).obj M where
  app X := AddCommGrpCat.ofHom
    ((zmultiplesHom (((underlyingPresheaf R).obj M).obj X) (s.1 X)).comp
      AddEquiv.ulift.toAddMonoidHom)
  naturality {X Y} f := by
    ext k
    change k.down • s.1 Y = (((underlyingPresheaf R).obj M).map f).hom (k.down • s.1 X)
    exact (congrArg (fun x => k.down • x) (s.2 f).symm).trans
      (map_zsmul (((underlyingPresheaf R).obj M).map f).hom k.down (s.1 X)).symm

/-- **Maps from the constant presheaf `ℤ` to a module are its global sections**: a map goes to
its family of values at `1`, and a compatible family `s` to the maps `n ↦ n • s`. -/
def globalSectionsHomAddEquiv (M : SheafOfModules.{u} R) :
    (constantInt.{u} C ⟶ (underlyingPresheaf R).obj M) ≃+ M.sections where
  toFun := sectionsOfConstantIntHom R M
  invFun := constantIntHomOfSections R M
  left_inv α := by
    ext X k
    change k.down • α.app X (ULift.up 1) = α.app X k
    refine (map_zsmul (α.app X).hom k.down (ULift.up 1)).symm.trans (congrArg (α.app X).hom ?_)
    exact ULift.ext (by simp)
  right_inv s := Subtype.ext (funext fun X => one_smul ℤ (s.1 X))
  map_add' _ _ := rfl

/-- `Stacks.SheafOfModules.globalSectionsHom` is the global sections functor followed by the
forgetful functor to abelian groups. -/
def globalSectionsHomIso : globalSectionsHom R ≅
    Stacks.Cohomology.SiteModules.globalSectionsFunctor R ⋙
      forget₂ (ModuleCat.{max w u} (RingCat.sectionsSubring R.obj)) AddCommGrpCat.{max w u} :=
  NatIso.ofComponents (fun M => (globalSectionsHomAddEquiv R M).toAddCommGrpIso) fun _ => by
    ext
    rfl


/-- Vanishing of the derived functors of `globalSectionsHom` gives that of the global sections
functor. -/
private theorem isZero_rightDerived_globalSectionsFunctor_of_globalSectionsHom
    [EnoughInjectives (SheafOfModules.{u} R)] [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] (n : ℕ) (M : SheafOfModules.{u} R)
    (h : IsZero (((globalSectionsHom R).rightDerived n).obj M)) :
    IsZero (((Stacks.Cohomology.SiteModules.globalSectionsFunctor R).rightDerived n).obj M) := by
  have h := Stacks.Cohomology.RightDerivedCoEdge.isZero_rightDerived_obj_of_iso
    (globalSectionsHomIso R) n M h
  obtain ⟨e⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology
    (Stacks.Cohomology.SiteModules.globalSectionsFunctor R)
    (forget₂ (ModuleCat.{max w u} (RingCat.sectionsSubring R.obj)) AddCommGrpCat.{max w u}) n M
  exact (ModuleCat.isZero_iff_subsingleton).2
    ((AddCommGrpCat.isZero_iff_subsingleton).1 (h.of_iso e))


/-- **The Koszul complex of sections computes the cohomology of a sheaf of modules**, in the
vanishing form: if `U` covers the final object, `M` is acyclic for every term `Hom(Q_p, -)`
and `Hom(Q_p, M) = 0` for `p ≥ d`, then `Hⁿ(M) = 0` for every `n ≥ d`. -/
theorem isZero_rightDerived_globalSectionsFunctor_of_koszulSections
    [EnoughInjectives (SheafOfModules.{u} R)] [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {U : C} {ι : Type*}
    (hU : J.CoversTop fun _ : ι => U) (M : SheafOfModules.{u} R)
    (hM : Stacks.Cohomology.RightDerivedCoEdge.IsComponentAcyclic (koszulSections R U) M)
    (d : ℕ) (hd : ∀ p, d ≤ p → IsZero (((koszulSections R U).obj M).X p)) (n : ℕ)
    (hn : d ≤ n) :
    IsZero (((Stacks.Cohomology.SiteModules.globalSectionsFunctor R).rightDerived
      n).obj M) := by
  exact isZero_rightDerived_globalSectionsFunctor_of_globalSectionsHom R n M
    (isZero_rightDerived_globalSectionsHom R hU M hM d hd n hn)

/-- **The Koszul complex of sections bounds the cohomology by partially acyclic terms**, in the
vanishing form: if `U` covers the final object, the terms `Hom(Q_p, -)` vanish for `p ≥ d`, and
`Rᵠ Hom(Q_p, -)(M) = 0` for `q ≥ eₚ` with every `eₚ ≥ 1`, then `Hⁿ(M) = 0` as soon as
`p + eₚ ≤ n` for every `p < d`.  This is the vanishing read off the first page of the
alternating Čech spectral sequence of [Stacks, Tag 0728], as in the proof of
[Stacks, Tag 072C]. -/
theorem isZero_rightDerived_globalSectionsFunctor_of_koszulSections_of_isZero_rightDerived
    [EnoughInjectives (SheafOfModules.{u} R)] [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {U : C} {ι : Type*}
    (hU : J.CoversTop fun _ : ι => U) (d : ℕ)
    (hd : ∀ p, d ≤ p → ∀ N : SheafOfModules.{u} R, IsZero (((koszulSections R U).obj N).X p))
    (M : SheafOfModules.{u} R) (e : ℕ → ℕ) (he1 : ∀ p, 0 < e p)
    (he : ∀ p q, e p ≤ q → IsZero
      (((Stacks.Cohomology.RightDerivedCoEdge.component (koszulSections R U) p).rightDerived
        q).obj M))
    (n : ℕ) (hn : ∀ p, p < d → p + e p ≤ n) :
    IsZero (((Stacks.Cohomology.SiteModules.globalSectionsFunctor R).rightDerived
      n).obj M) := by
  exact isZero_rightDerived_globalSectionsFunctor_of_globalSectionsHom R n M
    (isZero_rightDerived_globalSectionsHom_of_isZero_rightDerived R hU d hd M e he1 he n hn)

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space.SmallEtale

open Stacks.SheafOfModules

attribute [local instance] enoughInjectives_modules hasInjectiveResolutions_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

variable (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X.obj) (hc : IsEtale B S hS c)
    (hsep : IsSeparated B S hS (SpacesEtale.chartObj B S hS X W c hc).obj.hom.hom) (n : ℕ)

/-! ### Anti-invariant sections as a retract of all sections -/

/-- The sections over the chart of the complement of the diagonals, as a functor to abelian
groups in the universe of the Koszul complex of sections. -/
abbrev diagonalComplementSections :
    Modules.{u, u} B S hS X.1 X.2 ⥤ AddCommGrpCat.{u + 1} :=
  Stacks.Cohomology.SiteInverseLimits.sectionsFunctor (smallEtaleRingedSite B S hS X.1 X.2)
      (diagonalComplementChart B S hS X W c hc hsep n) ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- The module `M`, read as an abelian sheaf. -/
abbrev moduleSheaf (M : Modules.{u, u} B S hS X.1 X.2) :
    Sheaf (topology B S hS X.1) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj M

/-- The anti-invariant section of a module corresponding to a map out of `∧^{n+1} ℤ[h_U]`. -/
def koszulTermToSections :
    koszulSectionsTerm
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
        (etaleChart B S hS X W c hc) n ⟶
      diagonalComplementSections B S hS X W c hc hsep n where
  app M := AddCommGrpCat.ofHom
    { toFun := fun α => ULift.up
        (wedgeHomEquiv B S hS X W c hc hsep n (moduleSheaf B S hS X M) α).1
      map_zero' := by
        ext
        exact congrArg Subtype.val
          (map_zero (wedgeHomEquiv B S hS X W c hc hsep n (moduleSheaf B S hS X M)))
      map_add' := fun α β => by
        ext
        exact congrArg Subtype.val
          (map_add (wedgeHomEquiv B S hS X W c hc hsep n (moduleSheaf B S hS X M)) α β) }
  naturality M N φ := by
    ext α
    rfl

/-- Restriction of sections of a module along a morphism of charts, as an additive map. -/
abbrev restrictSections (M : Modules.{u, u} B S hS X.1 X.2) {V V' : SmallEtale B S hS X.1}
    (f : V' ⟶ V) : M.val.obj (op V) →+ M.val.obj (op V') :=
  ((moduleSheaf B S hS X M).obj.map f.op).hom

/-- Restricting along `f` and then along `g` is restricting along `g ≫ f`. -/
theorem restrictSections_comp (M : Modules.{u, u} B S hS X.1 X.2)
    {V V' V'' : SmallEtale B S hS X.1} (f : V' ⟶ V) (g : V'' ⟶ V') (x : M.val.obj (op V)) :
    restrictSections B S hS X M g (restrictSections B S hS X M f x) =
      restrictSections B S hS X M (g ≫ f) x := by
  simp only [restrictSections, op_comp]
  exact (Functor.map_comp_apply (((SheafOfModules.toSheaf
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj M).obj)
    f.op g.op x).symm

variable (t : Γ(chartScheme (diagonalComplementChart B S hS X W c hc hsep n), ⊤))

/-- The function `t`, read as a section of the structure sheaf over the chart of the complement
of the diagonals. -/
abbrev chartFunction :
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
      (op (diagonalComplementChart B S hS X W c hc hsep n)) :=
  t

/-- **The projection onto the anti-invariant sections** `s ↦ ∑_σ sign(σ) σ^*(t s)`, for a
function `t` on the complement of the diagonals. -/
def antiInvariantProjection (M : Modules.{u, u} B S hS X.1 X.2) :
    M.val.obj (op (diagonalComplementChart B S hS X W c hc hsep n)) →+
      M.val.obj (op (diagonalComplementChart B S hS X W c hc hsep n)) :=
  ∑ σ : Equiv.Perm (Fin (n + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
    (restrictSections B S hS X M (diagonalComplementChartAut B S hS X W c hc hsep n σ).asIso.hom).comp
      (AddMonoidHom.mk' (fun s => chartFunction B S hS X W c hc hsep n t • s)
        fun a b => smul_add _ a b)

/-- The anti-invariant projection sends `s` to `∑_σ sign(σ) σ^*(t s)`. -/
theorem antiInvariantProjection_apply (M : Modules.{u, u} B S hS X.1 X.2)
    (s : M.val.obj (op (diagonalComplementChart B S hS X W c hc hsep n))) :
    antiInvariantProjection B S hS X W c hc hsep n t M s =
      ∑ σ : Equiv.Perm (Fin (n + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
        restrictSections B S hS X M (diagonalComplementChartAut B S hS X W c hc hsep n σ).asIso.hom
          (chartFunction B S hS X W c hc hsep n t • s) := by
  simp [antiInvariantProjection]

/-- The automorphism of the complement of the diagonals attached to a product `σ * τ` of
permutations is the composite of the automorphism of `τ` followed by that of `σ`. -/
theorem diagonalComplementChartAut_mul_hom (σ τ : Equiv.Perm (Fin (n + 1))) :
    (diagonalComplementChartAut B S hS X W c hc hsep n (σ * τ)).asIso.hom =
      (diagonalComplementChartAut B S hS X W c hc hsep n τ).asIso.hom ≫
        (diagonalComplementChartAut B S hS X W c hc hsep n σ).asIso.hom := by
  rw [map_mul, Aut.mul_asIso]
  rfl

/-- The projection lands in the anti-invariant sections. -/
theorem antiInvariantProjection_mem (M : Modules.{u, u} B S hS X.1 X.2)
    (s : M.val.obj (op (diagonalComplementChart B S hS X W c hc hsep n))) :
    antiInvariantProjection B S hS X W c hc hsep n t M s ∈
      characterSections (diagonalComplementChart B S hS X W c hc hsep n)
        (diagonalComplementChartAut B S hS X W c hc hsep n) Equiv.Perm.sign
        ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)).obj M).obj := by
  intro τ
  let V := diagonalComplementChart B S hS X W c hc hsep n
  let a := diagonalComplementChartAut B S hS X W c hc hsep n
  let f : Equiv.Perm (Fin (n + 1)) → M.val.obj (op V) := fun σ =>
    restrictSections B S hS X M (a σ).asIso.hom (chartFunction B S hS X W c hc hsep n t • s)
  have key : restrictSections B S hS X M (a τ).asIso.hom
      (antiInvariantProjection B S hS X W c hc hsep n t M s) =
      ((Equiv.Perm.sign τ : ℤˣ) : ℤ) • antiInvariantProjection B S hS X W c hc hsep n t M s := by
    rw [antiInvariantProjection_apply, map_sum]
    have h1 : ∀ σ : Equiv.Perm (Fin (n + 1)),
        restrictSections B S hS X M (a τ).asIso.hom (((Equiv.Perm.sign σ : ℤˣ) : ℤ) • f σ) =
          ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • f (σ * τ) := by
      intro σ
      rw [map_zsmul]
      congr 1
      show restrictSections B S hS X M (a τ).asIso.hom (restrictSections B S hS X M (a σ).asIso.hom _) = _
      rw [restrictSections_comp, ← diagonalComplementChartAut_mul_hom]
    rw [Finset.sum_congr rfl fun σ _ => h1 σ]
    have h2 : (∑ σ : Equiv.Perm (Fin (n + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • f (σ * τ)) =
        ∑ ρ : Equiv.Perm (Fin (n + 1)), ((Equiv.Perm.sign (ρ * τ⁻¹) : ℤˣ) : ℤ) • f ρ :=
      Fintype.sum_equiv (Equiv.mulRight τ) _ _ fun σ => by simp
    rw [h2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [smul_smul]
    congr 1
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, Units.val_mul, mul_comm]
  exact key

/-- The projection is the identity on the anti-invariant sections, when `t` has trace `1`. -/
theorem antiInvariantProjection_eq_self
    (ht : ∑ σ : Equiv.Perm (Fin (n + 1)), autPullback B S hS X W c hc hsep n σ t = 1)
    (M : Modules.{u, u} B S hS X.1 X.2)
    (s : M.val.obj (op (diagonalComplementChart B S hS X W c hc hsep n)))
    (hs : s ∈ characterSections (diagonalComplementChart B S hS X W c hc hsep n)
        (diagonalComplementChartAut B S hS X W c hc hsep n) Equiv.Perm.sign
        ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)).obj M).obj) :
    antiInvariantProjection B S hS X W c hc hsep n t M s = s := by
  rw [antiInvariantProjection_apply]
  have hterm : ∀ σ : Equiv.Perm (Fin (n + 1)), ((Equiv.Perm.sign σ : ℤˣ) : ℤ) •
      restrictSections B S hS X M (diagonalComplementChartAut B S hS X W c hc hsep n σ).asIso.hom
        (chartFunction B S hS X W c hc hsep n t • s) =
      chartFunction B S hS X W c hc hsep n (autPullback B S hS X W c hc hsep n σ t) • s := by
    intro σ
    have h1 : restrictSections B S hS X M (diagonalComplementChartAut B S hS X W c hc hsep n σ).asIso.hom
        (chartFunction B S hS X W c hc hsep n t • s) =
        chartFunction B S hS X W c hc hsep n (autPullback B S hS X W c hc hsep n σ t) •
          restrictSections B S hS X M (diagonalComplementChartAut B S hS X W c hc hsep n σ).asIso.hom s :=
      M.val.map_smul (diagonalComplementChartAut B S hS X W c hc hsep n σ).asIso.hom.op
        (chartFunction B S hS X W c hc hsep n t) s
    rw [h1]
    have h2 : restrictSections B S hS X M (diagonalComplementChartAut B S hS X W c hc hsep n σ).asIso.hom
        s = ((Equiv.Perm.sign σ : ℤˣ) : ℤ) • s := hs σ
    rw [h2, smul_comm, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
  simp_rw [hterm]
  rw [← Finset.sum_smul]
  have ht' : (∑ σ : Equiv.Perm (Fin (n + 1)),
      chartFunction B S hS X W c hc hsep n (autPullback B S hS X W c hc hsep n σ t)) = 1 := ht
  rw [ht']
  exact one_smul _ s

/-- The projection is natural in the module. -/
theorem antiInvariantProjection_naturality {M N : Modules.{u, u} B S hS X.1 X.2} (φ : M ⟶ N)
    (s : M.val.obj (op (diagonalComplementChart B S hS X W c hc hsep n))) :
    φ.val.app _ (antiInvariantProjection B S hS X W c hc hsep n t M s) =
      antiInvariantProjection B S hS X W c hc hsep n t N (φ.val.app _ s) := by
  rw [antiInvariantProjection_apply, antiInvariantProjection_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_zsmul]
  congr 1
  have hnat := NatTrans.naturality_apply
    ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)).map φ).hom
    (diagonalComplementChartAut B S hS X W c hc hsep n σ).asIso.hom.op
    (chartFunction B S hS X W c hc hsep n t • s)
  refine hnat.trans ?_
  congr 1
  exact (φ.val.app _).hom.map_smul _ s

variable (ht : ∑ σ : Equiv.Perm (Fin (n + 1)), autPullback B S hS X W c hc hsep n σ t = 1)

/-- The map out of `∧^{n+1} ℤ[h_U]` attached to the anti-invariant projection of a section over
the chart of the complement of the diagonals, for one module. -/
def sectionsToKoszulTermApp (M : Modules.{u, u} B S hS X.1 X.2) :
    M.val.obj (op (diagonalComplementChart B S hS X W c hc hsep n)) →+
      (chartExteriorPower B S hS X W c hc n ⟶ (moduleSheaf B S hS X M).obj) :=
  (wedgeHomEquiv B S hS X W c hc hsep n (moduleSheaf B S hS X M)).symm.toAddMonoidHom.comp
    ((antiInvariantProjection B S hS X W c hc hsep n t M).codRestrict _
      (antiInvariantProjection_mem B S hS X W c hc hsep n t M))

/-- The anti-invariant section corresponding to the map attached to `s` is the anti-invariant
projection of `s`. -/
theorem wedgeHomEquiv_sectionsToKoszulTermApp (M : Modules.{u, u} B S hS X.1 X.2)
    (s : M.val.obj (op (diagonalComplementChart B S hS X W c hc hsep n))) :
    (wedgeHomEquiv B S hS X W c hc hsep n (moduleSheaf B S hS X M)
        (sectionsToKoszulTermApp B S hS X W c hc hsep n t M s)).1 =
      antiInvariantProjection B S hS X W c hc hsep n t M s :=
  congrArg Subtype.val (AddEquiv.apply_symm_apply _ _)

/-- The map out of `∧^{n+1} ℤ[h_U]` attached to the anti-invariant projection of a section over
the chart of the complement of the diagonals. -/
def sectionsToKoszulTerm :
    diagonalComplementSections B S hS X W c hc hsep n ⟶
      koszulSectionsTerm
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
        (etaleChart B S hS X W c hc) n where
  app M := AddCommGrpCat.ofHom
    ((sectionsToKoszulTermApp B S hS X W c hc hsep n t M).comp AddEquiv.ulift.toAddMonoidHom)
  naturality M N φ := by
    ext m
    apply (wedgeHomEquiv B S hS X W c hc hsep n (moduleSheaf B S hS X N)).injective
    refine Subtype.ext ?_
    refine Eq.symm ?_
    exact (congrArg (fun x => ((SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)).map φ).hom.app
          (op (diagonalComplementChart B S hS X W c hc hsep n)) x)
        (wedgeHomEquiv_sectionsToKoszulTermApp B S hS X W c hc hsep n t M m.down)).trans
      ((antiInvariantProjection_naturality B S hS X W c hc hsep n t φ m.down).trans
        (wedgeHomEquiv_sectionsToKoszulTermApp B S hS X W c hc hsep n t N _).symm)

include ht in
/-- When `t` has trace `1`, `sectionsToKoszulTerm` is a retraction of `koszulTermToSections`. -/
theorem koszulTermToSections_comp_sectionsToKoszulTerm :
    koszulTermToSections B S hS X W c hc hsep n ≫ sectionsToKoszulTerm B S hS X W c hc hsep n t =
      𝟙 _ := by
  ext M α
  change chartExteriorPower B S hS X W c hc n ⟶ (moduleSheaf B S hS X M).obj at α
  apply (wedgeHomEquiv B S hS X W c hc hsep n (moduleSheaf B S hS X M)).injective
  refine Subtype.ext ?_
  exact (wedgeHomEquiv_sectionsToKoszulTermApp B S hS X W c hc hsep n t M _).trans
    (antiInvariantProjection_eq_self B S hS X W c hc hsep n t ht M _
      (wedgeHomEquiv B S hS X W c hc hsep n _ α).2)

/-! ### Acyclicity of quasi-coherent modules for the Koszul terms -/

include hsep in
/-- **A quasi-coherent module is acyclic for every term of the Koszul complex of sections** of
an affine étale chart `U ⟶ X` of a separated algebraic space.  The `n`-th term is the functor
of anti-invariant sections over the complement `W_n` of the diagonals, a natural direct summand
of the sections over `W_n` because the symmetric group acts freely on the affine scheme `W_n`;
and the sections over the affine `W_n` have no higher derived functors on quasi-coherent
modules. -/
theorem isZero_rightDerived_koszulSectionsTerm
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)) (hcA : IsAffineHom B S hS c)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) (q : ℕ) (hq : 0 < q) :
    IsZero (((koszulSectionsTerm
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
      (etaleChart B S hS X W c hc) n).rightDerived q).obj M) := by
  obtain ⟨t, ht⟩ := exists_sum_autPullback_eq_one B S hS X W c hc hsep n hW hcA
  have hD :
      IsZero (((diagonalComplementSections B S hS X W c hc hsep n).rightDerived q).obj M) := by
    obtain ⟨e⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology
      (Stacks.Cohomology.SiteInverseLimits.sectionsFunctor (smallEtaleRingedSite B S hS X.1 X.2)
        (diagonalComplementChart B S hS X W c hc hsep n)) AddCommGrpCat.uliftFunctor.{u + 1, u} q M
    exact (Functor.map_isZero _ (isZero_rightDerived_sectionsFunctor_of_isAffineChart B S hS X.1
      X.2 M hM _ (isAffine_chartScheme_diagonalComplementChart B S hS X W c hc hsep n hW hcA) q
        hq)).of_iso e.symm
  exact Stacks.Cohomology.RightDerivedCoEdge.isZero_rightDerived_obj_of_retract
    (koszulTermToSections B S hS X W c hc hsep n) (sectionsToKoszulTerm B S hS X W c hc hsep n t)
    (koszulTermToSections_comp_sectionsToKoszulTerm B S hS X W c hc hsep n t ht) q M hD

/-! ### Vanishing of the Koszul terms above the fibre bound -/

include hsep in
/-- **Above the fibre bound the complement of the diagonals has no points**: if every family of
pairwise distinct lifts of a field-valued point of `X` through the chart has at most `d`
members, then the complement of the diagonals in the `(n+1)`-fold self-product of the chart is
empty for `n ≥ d`. -/
theorem isEmpty_points_comparisonFunctor_diagonalComplementChart (d : ℕ)
    (hd : ∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
      (ξ : yoneda.obj T ⟶ X.obj) (m : ℕ) (w : Fin m → (T ⟶ W)),
        (∀ k, yoneda.map (w k) ≫ c = ξ) → Function.Injective w → m ≤ d)
    (hn : d ≤ n) :
    IsEmpty (points B S hS (SpacesEtale.underlying B S hS X
      ((comparisonFunctor B S hS X).obj
        (diagonalComplementChart B S hS X W c hc hsep n))).obj) := by
  have h := SpacesEtale.isEmpty_points_diagonalComplement_of_forall_le B S hS X W c hc hsep d hd
    (n + 1) (Nat.lt_succ_of_le hn)
  exact ⟨fun x => h.false (pointsMap B S hS _ ((SpacesEtale.toSpaces B S hS X).map
    (comparisonDiagonalComplementChartIso B S hS X W c hc hsep n).hom).hom x)⟩

include hsep in
/-- **The Koszul terms vanish above the fibre bound**: for `n ≥ d` the module of maps from
`∧^{n+1} ℤ[h_U]` to any module is zero, because these maps are anti-invariant sections over an
empty chart. -/
theorem isZero_koszulSectionsTerm_obj (d : ℕ)
    (hd : ∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
      (ξ : yoneda.obj T ⟶ X.obj) (m : ℕ) (w : Fin m → (T ⟶ W)),
        (∀ k, yoneda.map (w k) ≫ c = ξ) → Function.Injective w → m ≤ d)
    (hn : d ≤ n) (M : Modules.{u, u} B S hS X.1 X.2) :
    IsZero ((koszulSectionsTerm
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
      (etaleChart B S hS X W c hc) n).obj M) := by
  have hz := CategoryTheory.Sheaf.isZero_obj_of_bot_mem (moduleSheaf B S hS X M)
    (bot_mem_topology_of_isEmpty_points B S hS X
      (isEmpty_points_comparisonFunctor_diagonalComplementChart B S hS X W c hc hsep n d hd hn))
  have hsub : Subsingleton ((moduleSheaf B S hS X M).obj.obj
      (op (diagonalComplementChart B S hS X W c hc hsep n))) :=
    AddCommGrpCat.isZero_iff_subsingleton.1 hz
  refine AddCommGrpCat.isZero_iff_subsingleton.2 ⟨fun a b => ?_⟩
  change chartExteriorPower B S hS X W c hc n ⟶ (moduleSheaf B S hS X M).obj at a b
  exact (wedgeHomEquiv B S hS X W c hc hsep n (moduleSheaf B S hS X M)).injective
    (Subtype.ext (Subsingleton.elim _ _))

end AlgebraicGeometry.Space.SmallEtale

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules

attribute [local instance] enoughInjectives_modules hasInjectiveResolutions_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 072B.**  Let `X` be a separated algebraic space, `U` an affine scheme and
`f : U → X` a surjective étale morphism whose base changes to fields are finite locally free of
degree at most `d`.  Then `Hᵠ(X, ℱ) = 0` for every quasi-coherent `𝒪_X`-module `ℱ` and every
`q ≥ d`. -/
@[stacks 072B "The reading of d as a degree bound: the base changes of f to fields have degree \
  at most d, which is what the source's proof uses and what Lemma 69.7.3 (Tag 072C) supplies. \
  The literal reading (at most d points in each fibre of |U| → |X|) is neither proved nor \
  refuted here; for it the proof's step W_p = ∅ for p ≥ d fails (Spec k' → Spec k with k'/k \
  separable quadratic: one point per fibre, degree 2), although the conclusion holds in that \
  example. Quasi-compactness of X is implied by the affine surjection and not assumed."]
theorem isZero_rightDerived_globalSectionsFunctor_of_isSeparated
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (hsepX : IsAbsolutelySeparated B S hS hZ X.1)
    (W : BigFppfOver B S hS) (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (c : yoneda.obj W ⟶ X.obj) (hc : IsEtale B S hS c) (hsurj : IsSurjective B S hS c)
    (d : ℕ) (hd : ∀ (k : Type u) [Field k] (T : BigFppfOver B S hS),
      ((BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of k)) →
      ∀ ξ : yoneda.obj T ⟶ X.obj,
        ∃ (V : BigFppfOver B S hS) (p : V ⟶ T) (i : yoneda.obj V ⟶ yoneda.obj W) (r : ℕ),
          r ≤ d ∧ Stacks.Morphisms.IsFiniteLocallyFreeOfRank
              ((BigFppfOver.toScheme B S hS).map p) r ∧
            IsPullback i (yoneda.map p) c ξ)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) (q : ℕ) (hq : d ≤ q) :
    IsZero (((Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived q).obj F) := by
  have hcA : IsAffineHom B S hS c :=
    isAffineHom_of_affine_source_of_isAbsolutelySeparated B S hS hZ ⟨W, hW⟩ c hsepX
  have hsep : IsSeparated B S hS c :=
    isSeparated_of_isAffineHom B S hS c (isAlgebraicSpace_yoneda B S hS W) X.2 hcA
  have hd' : ∀ (K : Type u) (_ : Field K) (T : BigFppfOver B S hS)
      (_ : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of K))
      (ξ : yoneda.obj T ⟶ X.obj) (m : ℕ) (w : Fin m → (T ⟶ W)),
        (∀ k, yoneda.map (w k) ≫ c = ξ) → Function.Injective w → m ≤ d := by
    intro K _ T eT ξ m w hw hwinj
    obtain ⟨V, p, i, r, hrle, hrank, hsq⟩ := hd K T eT ξ
    exact (le_of_injective_lifts_of_isFiniteLocallyFreeOfRank_fibre B S hS W c T eT ξ V p i r m
      hrank hsq w hw hwinj).trans hrle
  have := enoughInjectives_modules B S hS X.1 X.2
  have : HasSheafify (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u} :=
    SmallEtale.instHasSheafify B S hS X.1 AddCommGrpCat.{u}
  have : (smallEtaleRingedSite B S hS X.1 X.2).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    SmallEtale.instWEqualsLocallyBijective B S hS X.1 AddCommGrpCat.{u}
  refine isZero_rightDerived_globalSectionsFunctor_of_koszulSections
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
    (U := SmallEtale.etaleChart B S hS X W c hc)
    (SmallEtale.coversTop_of_isSurjective B S hS X.1 X.2 _ hsurj) F ?_ d ?_ q hq
  · intro p m hm
    exact Stacks.Cohomology.RightDerivedCoEdge.isZero_rightDerived_obj_of_iso
      (koszulSectionsComponentIso _ _ p).symm m F
      (SmallEtale.isZero_rightDerived_koszulSectionsTerm B S hS X W c hc hsep p hW hcA F hF m hm)
  · intro p hp
    exact SmallEtale.isZero_koszulSectionsTerm_obj B S hS X W c hc hsep p d hd' hp F

end AlgebraicGeometry.Space

end
