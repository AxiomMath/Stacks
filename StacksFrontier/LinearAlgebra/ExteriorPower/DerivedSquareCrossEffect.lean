module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.CategoryTheory.Monoidal.Tor
public import StacksFrontier.Algebra.Homology.HomologyFunctorLinear
public import StacksFrontier.Algebra.DifferentialGraded.Module.CanonicalDeltaFunctor
public import StacksFrontier.AlgebraicTopology.SimplicialTensorConnectivity
public import StacksFrontier.CategoryTheory.Abelian.Projective.Horseshoe
public import StacksFrontier.CategoryTheory.Sites.Modules.AdicQuotientModuleTower
public import StacksFrontier.LinearAlgebra.ExteriorPower.DerivedSquare
public import StacksFrontier.LinearAlgebra.ExteriorPower.SquareFiltration
public import StacksFrontier.RingTheory.Tor.AlmostFlatResolution
public import StacksFrontier.AlgebraicTopology.SimplicialTensorShortExact

/-!
# The cross effect of the derived exterior square

Let `A` be a commutative ring and `0 → M' →u M →v M'' → 0` a short exact sequence of
`A`-modules. This file compares the derived exterior squares `LΛ²(M')`, `LΛ²(M)`, `LΛ²(M'')`
of Dold and Puppe, computed by simplicial projective resolutions
(`Stacks.SimplicialProjectiveResolution`), through the cross term `Tor(M', M'')`.

**The simplicial horseshoe.** Given simplicial projective resolutions `P'` of `M'` and `P''`
of `M''`, the horseshoe lemma applied to their normalized Moore complexes gives a projective
resolution `K` of `M` and a degreewise split short exact sequence of projective resolutions
`N(P') → K → N(P'')` over `u` and `v`. The Dold–Kan functor `Γ` is an exact equivalence, and
`Γ(N(P)) ≅ P`, so `P' → Γ(K) → P''` is a short exact sequence of simplicial objects lying over
`u` and `v`, with `P = Γ(K)` a simplicial projective resolution of `M`. It is degreewise split
because the terms of `P''` are projective.

**Two filtrations.** Degreewise, with `Fil ⊆ Λ²P` spanned by the wedges `u p' ∧ p`, there are
natural short exact sequences `0 → Λ²P' → Fil → P' ⊗ P'' → 0` and `0 → Fil → Λ²P → Λ²P'' → 0`
(`Stacks.ExteriorSquare.filtrationShortComplex`,
`Stacks.ExteriorSquare.exteriorSquareShortComplex`).
Writing `Q = Λ²P/Λ²P'`, the third isomorphism theorem gives two more,
`0 → Λ²P' → Λ²P → Q → 0` and `0 → P' ⊗ P'' → Q → Λ²P'' → 0`. Their Moore complexes give four
long exact homology sequences, in which the maps `L_iΛ²(P') → L_iΛ²(P)` and
`L_iΛ²(P) → L_iΛ²(P'')` are the maps `L_iΛ²(u)` and `L_iΛ²(v)` on derived exterior squares.

**The cross term.** The augmentation `P'' → M''` is degreewise surjective with acyclic kernel
`K''`. Tensoring with the degreewise flat `P'` preserves acyclicity: this is proved by
induction on the degree with the reduced décalage, which covers `K''` by a simplicial module
that is simplicially null-homotopic, also after tensoring. Hence `P' ⊗ P'' → P' ⊗ M''` is a
quasi-isomorphism of Moore complexes, and `H_i(P' ⊗ M'') = H_i(N(P') ⊗ M'') = Tor_i(M', M'')`.

**Multiplication by a nonzerodivisor.** If `M' = M` and `u` is multiplication by `c ∈ A`, the map
`L_iΛ²(u)` is multiplication by `c²`, since `Λ²(c • id) = c² • id`. The long exact sequence of
`0 → Λ²P' → Λ²P → Q → 0` then exhibits `H_*(Q)` as the homology of the cone of multiplication
by `c²` on `LΛ²(M)`, and that of `0 → P' ⊗ P'' → Q → Λ²P'' → 0` relates it to
`Tor_*(M, M/cM)` and `LΛ²(M/cM)`.

## Main definitions

* `Stacks.SimplicialHorseshoe S`: simplicial projective resolutions of the three terms of a short
  complex `S`, with a short exact sequence of simplicial objects between them lying over `S`.
* `Stacks.SimplicialHorseshoe.ofResolutions`: the simplicial horseshoe built on given
  resolutions of the outer terms.
* `Stacks.SimplicialProjectiveResolution.toConst`: the augmentation of a simplicial projective
  resolution, as a morphism to the constant simplicial object.
* `Stacks.SimplicialProjectiveResolution.homologyTensorIsoTor`: `H_i(P ⊗ Q) ≅ Tor_i(M, N)`.
* `Stacks.DerivedSquare.filtrationSequence`, `Stacks.DerivedSquare.exteriorSquareSequence`,
  `Stacks.DerivedSquare.quotientSequence`, `Stacks.DerivedSquare.crossSequence`: the four short
  exact sequences of simplicial modules attached to a simplicial horseshoe, and
  `Stacks.DerivedSquare.filtrationδ`, `Stacks.DerivedSquare.exteriorSquareδ`,
  `Stacks.DerivedSquare.quotientδ`, `Stacks.DerivedSquare.crossδ` their connecting morphisms.
* `Stacks.DerivedSquare.crossHomologyIsoTor`: `H_i(P' ⊗ P'') ≅ Tor_i(M', M'')`.

## Main results

* `Stacks.SimplicialHorseshoe.isSplitMono_f_app`: a simplicial horseshoe is degreewise split.
* `Stacks.isZero_homology_tensor_of_acyclic`: tensoring with a degreewise flat simplicial module
  preserves acyclicity of Moore complexes.
* `Stacks.DerivedSquare.exact_filtration_middle` and its eleven siblings: exactness of the four
  long exact sequences at every term.
* `Stacks.DerivedSquare.homologyMap_wedgeι_comp_homologyMap_filtrationι`,
  `Stacks.DerivedSquare.homologyMap_whiskerRight_f`,
  `Stacks.DerivedSquare.homologyMap_whiskerRight_g`: the maps of the long exact sequences between
  derived exterior squares are the derived maps of `u` and `v`.
* `Stacks.DerivedSquare.derivedMap_smul_id`: `LΛ²(c • id) = c² • id`.
* `Stacks.DerivedSquare.exact_quotient_smul_middle`,
  `Stacks.DerivedSquare.exact_quotient_smul_right`,
  `Stacks.DerivedSquare.exact_quotient_smul_left`: the long exact sequence of the cone of
  multiplication by `c²` on `LΛ²(M)`.

## Implementation notes

The cone of the degreewise injective map `Λ²P' → Λ²P` is replaced by its cokernel `Q`; the two
have isomorphic homology, and `Q` is what the third isomorphism theorem applies to. The Tor
groups are Mathlib's `CategoryTheory.Tor'`, the left derived functors of `- ⊗ M''` evaluated at
`M'`, computed by the normalized Moore complex of `P'`. The derived exterior squares are
computed by the resolutions of the horseshoe; the comparison isomorphisms
`Stacks.SimplicialProjectiveResolution.derivedIso` identify them with those of any other
resolutions.

## References

* A. Dold, D. Puppe, *Homologie nicht-additiver Funktoren. Anwendungen*, Ann. Inst. Fourier 11
  (1961), 201–312.
* L. Illusie, *Complexe cotangent et déformations I*, Lecture Notes in Math. 239 (1971),
  chapitre I, §4.
* C. Weibel, *An introduction to homological algebra*, Lemma 2.2.8.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite Simplicial

universe v u

namespace Stacks

/-! ### The Dold–Kan equivalence, with its functors spelled `N` and `Γ` -/

namespace DoldKan

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The Dold–Kan functor `Γ` is an equivalence. -/
instance : (Abelian.DoldKan.Γ (A := C)).IsEquivalence :=
  inferInstanceAs (Abelian.DoldKan.equivalence (A := C)).inverse.IsEquivalence

/-- The unit `X ⟶ Γ(N(X))` of the Dold–Kan equivalence. -/
def unit (X : SimplicialObject C) :
    X ⟶ Abelian.DoldKan.Γ.obj ((normalizedMooreComplex C).obj X) :=
  (Abelian.DoldKan.equivalence (A := C)).unit.app X

/-- The inverse `Γ(N(X)) ⟶ X` of the unit of the Dold–Kan equivalence. -/
def unitInv (X : SimplicialObject C) :
    Abelian.DoldKan.Γ.obj ((normalizedMooreComplex C).obj X) ⟶ X :=
  (Abelian.DoldKan.equivalence (A := C)).unitInv.app X

/-- The counit `N(Γ(K)) ⟶ K` of the Dold–Kan equivalence. -/
def counit (K : ChainComplex C ℕ) :
    (normalizedMooreComplex C).obj (Abelian.DoldKan.Γ.obj K) ⟶ K :=
  (Abelian.DoldKan.equivalence (A := C)).counit.app K

/-- The unit of the Dold–Kan equivalence followed by its inverse is the identity. -/
@[reassoc (attr := simp)]
lemma unit_comp_unitInv (X : SimplicialObject C) : unit X ≫ unitInv X = 𝟙 X :=
  (Abelian.DoldKan.equivalence (A := C)).unitIso.hom_inv_id_app X

/-- The inverse of the unit of the Dold–Kan equivalence followed by the unit is the identity. -/
@[reassoc (attr := simp)]
lemma unitInv_comp_unit (X : SimplicialObject C) : unitInv X ≫ unit X = 𝟙 _ :=
  (Abelian.DoldKan.equivalence (A := C)).unitIso.inv_hom_id_app X

/-- The unit `X ⟶ Γ(N(X))` of the Dold–Kan equivalence is an isomorphism. -/
instance (X : SimplicialObject C) : IsIso (unit X) :=
  ⟨unitInv X, unit_comp_unitInv X, unitInv_comp_unit X⟩

/-- The inverse `Γ(N(X)) ⟶ X` of the unit of the Dold–Kan equivalence is an isomorphism. -/
instance (X : SimplicialObject C) : IsIso (unitInv X) :=
  ⟨unit X, unitInv_comp_unit X, unit_comp_unitInv X⟩

/-- The counit of the Dold–Kan equivalence is natural. -/
@[reassoc]
lemma counit_naturality {K L : ChainComplex C ℕ} (φ : K ⟶ L) :
    (normalizedMooreComplex C).map (Abelian.DoldKan.Γ.map φ) ≫ counit L = counit K ≫ φ :=
  (Abelian.DoldKan.equivalence (A := C)).counit.naturality φ

/-- A triangle identity of the Dold–Kan equivalence. -/
@[reassoc (attr := simp)]
lemma map_unit_comp_counit (X : SimplicialObject C) :
    (normalizedMooreComplex C).map (unit X) ≫ counit ((normalizedMooreComplex C).obj X) = 𝟙 _ :=
  (Abelian.DoldKan.equivalence (A := C)).functor_unit_comp X

/-- `N` carries the inverse of the unit to the counit. -/
lemma map_unitInv (X : SimplicialObject C) :
    (normalizedMooreComplex C).map (unitInv X) = counit ((normalizedMooreComplex C).obj X) := by
  rw [← cancel_epi ((normalizedMooreComplex C).map (unit X)), ← Functor.map_comp,
    unit_comp_unitInv, CategoryTheory.Functor.map_id, map_unit_comp_counit]

end DoldKan

/-! ### The augmentation of a simplicial projective resolution -/

namespace SimplicialProjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] {X : C}

/-- The augmentation of the normalized Moore complex of `Γ(K)` is the counit of the Dold–Kan
equivalence followed by the augmentation of `K`. -/
lemma normalized_π_ofProjectiveResolution (K : ProjectiveResolution X) :
    (ofProjectiveResolution K).normalized.π = DoldKan.counit K.complex ≫ K.π := by
  have h : inclusionOfMooreComplexMap (Abelian.DoldKan.Γ.obj K.complex) ≫
      AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex _ = 𝟙 _ :=
    (AlgebraicTopology.DoldKan.splitMonoInclusionOfMooreComplexMap
      (Abelian.DoldKan.Γ.obj K.complex)).id
  change inclusionOfMooreComplexMap (Abelian.DoldKan.Γ.obj K.complex) ≫
    AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex _ ≫
      DoldKan.counit K.complex ≫ K.π = _
  rw [← Category.assoc, h]
  exact Category.id_comp _

/-- Any two vertices `g₁ g₂ : ⦋0⦌ ⟶ i` induce the same map `Pᵢ ⟶ X` after the augmentation. -/
lemma map_comp_ε_eq (P : SimplicialProjectiveResolution X) (i : SimplexCategory)
    (g₁ g₂ : ⦋0⦌ ⟶ i) : P.obj.map g₁.op ≫ P.ε = P.obj.map g₂.op ≫ P.ε := by
  induction i using SimplexCategory.rec with | _ n => ?_
  have key : ∀ (a b : Fin (n + 1)) (hab : a ≤ b) (h₁ h₂ : ⦋0⦌ ⟶ ⦋n⦌),
      h₁.toOrderHom 0 = a → h₂.toOrderHom 0 = b →
      P.obj.map h₁.op ≫ P.ε = P.obj.map h₂.op ≫ P.ε := by
    intro a b hab h₁ h₂ ha hb
    have e₁ : h₁ = SimplexCategory.δ 1 ≫ SimplexCategory.mkOfLe a b hab := by
      ext x
      fin_cases x
      simp [ha, SimplexCategory.mkOfLe, SimplexCategory.δ, Fin.succAbove]
      rfl
    have e₂ : h₂ = SimplexCategory.δ 0 ≫ SimplexCategory.mkOfLe a b hab := by
      ext x
      fin_cases x
      simp [hb, SimplexCategory.mkOfLe, SimplexCategory.δ]
      rfl
    rw [e₁, e₂, op_comp, op_comp, P.obj.map_comp, P.obj.map_comp, Category.assoc,
      Category.assoc]
    exact congrArg (P.obj.map (SimplexCategory.mkOfLe a b hab).op ≫ ·) (P.δ_zero_comp_ε).symm
  rcases le_total (g₁.toOrderHom 0) (g₂.toOrderHom 0) with h | h
  · exact key _ _ h g₁ g₂ rfl rfl
  · exact (key _ _ h g₂ g₁ rfl rfl).symm

/-- The augmentation `P ⟶ X` of a simplicial projective resolution, as a morphism to the constant
simplicial object: in degree `n` it is the map `Pₙ ⟶ P₀` induced by a vertex, followed by `ε`. -/
def toConst (P : SimplicialProjectiveResolution X) : P.obj ⟶ (SimplicialObject.const C).obj X :=
  (SimplicialObject.augment P.obj X P.ε P.map_comp_ε_eq).hom

/-- In degree `0`, the augmentation to the constant simplicial object is `ε`. -/
@[simp]
lemma toConst_app_zero (P : SimplicialProjectiveResolution X) :
    P.toConst.app (op ⦋0⦌) = P.ε :=
  SimplicialObject.augment_hom_zero _ _ _ _

variable (X) in
/-- The Moore complex of the constant simplicial object on `X` is homotopy equivalent to `X`
in degree `0`, through the extra degeneracy of the constant augmented object. -/
def constHomotopyEquiv : HomotopyEquiv ((alternatingFaceMapComplex C).obj
    ((SimplicialObject.const C).obj X)) ((ChainComplex.single₀ C).obj X) :=
  (SimplicialObject.Augmented.ExtraDegeneracy.const X).homotopyEquiv

variable (X) in
/-- In degree `0`, the homotopy equivalence `constHomotopyEquiv X` is the identity of `X`. -/
@[simp]
lemma constHomotopyEquiv_hom_f_zero : (constHomotopyEquiv X).hom.f 0 = 𝟙 X :=
  AlternatingFaceMapComplex.ε_app_f_zero _

/-- The homotopy equivalence `constHomotopyEquiv X` is a quasi-isomorphism. -/
instance quasiIso_constHomotopyEquiv_hom : QuasiIso (constHomotopyEquiv X).hom :=
  (constHomotopyEquiv X).quasiIso_hom

/-- The Moore complex of `toConst` followed by the homotopy equivalence of the constant
simplicial object with `X[0]` is the augmentation `π`. -/
lemma alternatingFaceMapComplex_map_toConst_comp (P : SimplicialProjectiveResolution X) :
    (alternatingFaceMapComplex C).map P.toConst ≫ (constHomotopyEquiv X).hom = P.π := by
  refine HomologicalComplex.to_single_hom_ext ?_
  rw [HomologicalComplex.comp_f, constHomotopyEquiv_hom_f_zero, alternatingFaceMapComplex_map_f,
    toConst_app_zero]
  exact Category.comp_id _

/-- The augmentation to the constant simplicial object induces a quasi-isomorphism of Moore
complexes. -/
instance quasiIso_alternatingFaceMapComplex_map_toConst (P : SimplicialProjectiveResolution X) :
    QuasiIso ((alternatingFaceMapComplex C).map P.toConst) := by
  have : QuasiIso ((alternatingFaceMapComplex C).map P.toConst ≫ (constHomotopyEquiv X).hom) := by
    rw [alternatingFaceMapComplex_map_toConst_comp]
    exact P.quasiIso
  exact quasiIso_of_comp_right (hφφ' := this) _ (constHomotopyEquiv X).hom

/-- The components of the augmentation to the constant simplicial object are epimorphisms. -/
instance epi_toConst_app (P : SimplicialProjectiveResolution X) (n : SimplexCategoryᵒᵖ) :
    Epi (P.toConst.app n) := by
  have hε : Epi P.ε := P.exact_ε.2
  have hsplit : IsSplitEpi (P.obj.map (SimplexCategory.const ⦋0⦌ n.unop 0).op) :=
    IsSplitEpi.mk' ⟨P.obj.map (SimplexCategory.const n.unop ⦋0⦌ 0).op, by
      rw [← P.obj.map_comp, ← op_comp, ← P.obj.map_id]
      congr 2
      ext x
      fin_cases x
      rfl⟩
  have : P.toConst.app n = P.obj.map (SimplexCategory.const ⦋0⦌ n.unop 0).op ≫ P.ε := rfl
  rw [this]
  infer_instance

end SimplicialProjectiveResolution

/-! ### The simplicial horseshoe -/

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A *simplicial horseshoe* over a short complex `S`: simplicial projective resolutions of
`S.X₁`, `S.X₂`, `S.X₃` and a short exact sequence `0 → P₁ → P₂ → P₃ → 0` of simplicial objects
whose maps lie over `S.f` and `S.g`. It is degreewise split, `isSplitMono_f_app`. -/
structure SimplicialHorseshoe (S : ShortComplex C) where
  /-- The resolution of `S.X₁`. -/
  P₁ : SimplicialProjectiveResolution S.X₁
  /-- The resolution of `S.X₂`. -/
  P₂ : SimplicialProjectiveResolution S.X₂
  /-- The resolution of `S.X₃`. -/
  P₃ : SimplicialProjectiveResolution S.X₃
  /-- The map `P₁ ⟶ P₂`. -/
  f : P₁.obj ⟶ P₂.obj
  /-- The map `P₂ ⟶ P₃`. -/
  g : P₂.obj ⟶ P₃.obj
  /-- The two maps compose to zero. -/
  w : f ≫ g = 0
  /-- The sequence `0 → P₁ → P₂ → P₃ → 0` is short exact. -/
  shortExact : (ShortComplex.mk f g w).ShortExact
  /-- The map `P₁ ⟶ P₂` lies over `S.f`. -/
  isLift_f : P₁.IsLift P₂ S.f f
  /-- The map `P₂ ⟶ P₃` lies over `S.g`. -/
  isLift_g : P₂.IsLift P₃ S.g g

namespace SimplicialHorseshoe

variable {S : ShortComplex C} (H : SimplicialHorseshoe S)

/-- The short exact sequence `0 → P₁ → P₂ → P₃ → 0` of a simplicial horseshoe. -/
abbrev ses : ShortComplex (SimplicialObject C) := ShortComplex.mk H.f H.g H.w

/-- A simplicial horseshoe is short exact in each degree. -/
lemma shortExact_app (n : SimplexCategoryᵒᵖ) :
    (H.ses.map ((evaluation SimplexCategoryᵒᵖ C).obj n)).ShortExact :=
  H.shortExact.map_of_exact _

/-- The map `P₁ ⟶ P₂` of a simplicial horseshoe is a monomorphism in each degree. -/
instance mono_f_app (n : SimplexCategoryᵒᵖ) : Mono (H.f.app n) := (H.shortExact_app n).mono_f

/-- The map `P₂ ⟶ P₃` of a simplicial horseshoe is an epimorphism in each degree. -/
instance epi_g_app (n : SimplexCategoryᵒᵖ) : Epi (H.g.app n) := (H.shortExact_app n).epi_g

/-- **A simplicial horseshoe is degreewise split**, because the terms of `P₃` are projective. -/
lemma isSplitMono_f_app (n : SimplexCategoryᵒᵖ) : IsSplitMono (H.f.app n) := by
  have hS := H.shortExact_app n
  have : Projective (H.ses.map ((evaluation SimplexCategoryᵒᵖ C).obj n)).X₃ :=
    H.P₃.projective n.unop.len
  have : Epi (H.ses.map ((evaluation SimplexCategoryᵒᵖ C).obj n)).g := hS.epi_g
  exact (ShortComplex.Splitting.ofExactOfSection _ hS.exact
    (Projective.factorThru (𝟙 _) (H.ses.map ((evaluation SimplexCategoryᵒᵖ C).obj n)).g)
    (Projective.factorThru_comp _ _) hS.mono_f).isSplitMono_f

section Construction

open ShortComplex.HorseshoeAux

variable (P₁ : SimplicialProjectiveResolution S.X₁) (P₃ : SimplicialProjectiveResolution S.X₃)
  (hS : S.ShortExact)

/-- The middle term of the horseshoe of the normalized Moore complexes of `P₁` and `P₃`. -/
abbrev chainResolution : ProjectiveResolution S.X₂ := PB P₁.normalized P₃.normalized hS

/-- The left map of the horseshoe of normalized Moore complexes. -/
def chainι : P₁.normalized.complex ⟶ (chainResolution P₁ P₃ hS).complex :=
  iota P₁.normalized P₃.normalized hS

/-- The right map of the horseshoe of normalized Moore complexes. -/
def chainπ : (chainResolution P₁ P₃ hS).complex ⟶ P₃.normalized.complex :=
  proj P₁.normalized P₃.normalized hS

/-- The two maps of the horseshoe of normalized Moore complexes compose to zero. -/
@[reassoc (attr := simp)]
lemma chainι_comp_chainπ : chainι P₁ P₃ hS ≫ chainπ P₁ P₃ hS = 0 :=
  iota_comp_proj P₁.normalized P₃.normalized hS

/-- The left map of the horseshoe of normalized Moore complexes lies over `S.f`. -/
lemma chainι_comp_π : chainι P₁ P₃ hS ≫ (chainResolution P₁ P₃ hS).π =
    P₁.normalized.π ≫ (ChainComplex.single₀ C).map S.f :=
  iota_comp_aug P₁.normalized P₃.normalized hS

/-- The right map of the horseshoe of normalized Moore complexes lies over `S.g`. -/
lemma chainπ_comp_π : chainπ P₁ P₃ hS ≫ P₃.normalized.π =
    (chainResolution P₁ P₃ hS).π ≫ (ChainComplex.single₀ C).map S.g :=
  proj_comp_π P₁.normalized P₃.normalized hS

/-- The horseshoe of normalized Moore complexes `N(P₁) → K → N(P₃)` is short exact. -/
lemma chain_shortExact : (ShortComplex.mk _ _ (chainι_comp_chainπ P₁ P₃ hS)).ShortExact :=
  ses_shortExact P₁.normalized P₃.normalized hS

/-- The middle resolution of the simplicial horseshoe: `Γ` of the middle term of the horseshoe of
normalized Moore complexes. -/
abbrev middle : SimplicialProjectiveResolution S.X₂ :=
  { SimplicialProjectiveResolution.ofProjectiveResolution (chainResolution P₁ P₃ hS) with
    obj := Abelian.DoldKan.Γ.obj (chainResolution P₁ P₃ hS).complex }

/-- The augmentation of the normalized Moore complex of `middle P₁ P₃ hS` is the counit of the
Dold–Kan equivalence followed by the augmentation of the horseshoe `K`. -/
lemma middle_normalized_π :
    (middle P₁ P₃ hS).normalized.π =
      DoldKan.counit (chainResolution P₁ P₃ hS).complex ≫ (chainResolution P₁ P₃ hS).π :=
  SimplicialProjectiveResolution.normalized_π_ofProjectiveResolution _

/-- The left map `P₁ ⟶ Γ(N(P₁)) ⟶ Γ(K)` of the simplicial horseshoe. -/
def simplicialι : P₁.obj ⟶ (middle P₁ P₃ hS).obj :=
  DoldKan.unit P₁.obj ≫ Abelian.DoldKan.Γ.map (chainι P₁ P₃ hS)

/-- The right map `Γ(K) ⟶ Γ(N(P₃)) ⟶ P₃` of the simplicial horseshoe. -/
def simplicialπ : (middle P₁ P₃ hS).obj ⟶ P₃.obj :=
  Abelian.DoldKan.Γ.map (chainπ P₁ P₃ hS) ≫ DoldKan.unitInv P₃.obj

/-- The two maps of the simplicial horseshoe compose to zero. -/
@[reassoc (attr := simp)]
lemma simplicialι_comp_simplicialπ : simplicialι P₁ P₃ hS ≫ simplicialπ P₁ P₃ hS = 0 := by
  rw [simplicialι, simplicialπ, Category.assoc, ← Functor.map_comp_assoc, chainι_comp_chainπ,
    Functor.map_zero, Limits.zero_comp, Limits.comp_zero]

/-- The sequence `0 → P₁ → Γ(K) → P₃ → 0` of simplicial objects is short exact. -/
lemma simplicial_shortExact :
    (ShortComplex.mk _ _ (simplicialι_comp_simplicialπ P₁ P₃ hS)).ShortExact := by
  refine ShortComplex.shortExact_of_iso ?_
    ((chain_shortExact P₁ P₃ hS).map_of_exact Abelian.DoldKan.Γ)
  exact ShortComplex.isoMk (asIso (DoldKan.unitInv P₁.obj)) (Iso.refl _)
    (asIso (DoldKan.unitInv P₃.obj)) (by simp [simplicialι]) (by simp [simplicialπ])

/-- The left map `P₁ ⟶ Γ(K)` of the simplicial horseshoe lies over `S.f`. -/
lemma isLift_simplicialι : P₁.IsLift (middle P₁ P₃ hS) S.f (simplicialι P₁ P₃ hS) := by
  rw [SimplicialProjectiveResolution.isLift_iff_normalized, middle_normalized_π,
    simplicialι, Functor.map_comp, Category.assoc, DoldKan.counit_naturality_assoc,
    chainι_comp_π, DoldKan.map_unit_comp_counit_assoc]

/-- The right map `Γ(K) ⟶ P₃` of the simplicial horseshoe lies over `S.g`. -/
lemma isLift_simplicialπ : (middle P₁ P₃ hS).IsLift P₃ S.g (simplicialπ P₁ P₃ hS) := by
  rw [SimplicialProjectiveResolution.isLift_iff_normalized, middle_normalized_π,
    simplicialπ, Functor.map_comp, Category.assoc, DoldKan.map_unitInv,
    DoldKan.counit_naturality_assoc, chainπ_comp_π, Category.assoc]

/-- **The simplicial horseshoe lemma.** For a short exact sequence `0 → S.X₁ → S.X₂ → S.X₃ → 0`
and given simplicial projective resolutions `P₁` of `S.X₁` and `P₃` of `S.X₃`, there are a
simplicial projective resolution `P₂` of `S.X₂` and a short exact sequence `0 → P₁ → P₂ → P₃ → 0`
of simplicial objects lying over `S`. Here `P₂ = Γ(K)` for the horseshoe `K` of the normalized
Moore complexes of `P₁` and `P₃`. -/
def ofResolutions : SimplicialHorseshoe S where
  P₁ := P₁
  P₂ := middle P₁ P₃ hS
  P₃ := P₃
  f := simplicialι P₁ P₃ hS
  g := simplicialπ P₁ P₃ hS
  w := simplicialι_comp_simplicialπ P₁ P₃ hS
  shortExact := simplicial_shortExact P₁ P₃ hS
  isLift_f := isLift_simplicialι P₁ P₃ hS
  isLift_g := isLift_simplicialπ P₁ P₃ hS

/-- The resolution of `S.X₁` in `ofResolutions P₁ P₃ hS` is `P₁`. -/
@[simp]
lemma ofResolutions_P₁ : (ofResolutions P₁ P₃ hS).P₁ = P₁ := rfl

/-- The resolution of `S.X₃` in `ofResolutions P₁ P₃ hS` is `P₃`. -/
@[simp]
lemma ofResolutions_P₃ : (ofResolutions P₁ P₃ hS).P₃ = P₃ := rfl

end Construction

/-- Every short exact sequence in an abelian category with projective resolutions has a
simplicial horseshoe. -/
theorem nonempty [HasProjectiveResolutions C] (hS : S.ShortExact) :
    Nonempty (SimplicialHorseshoe S) :=
  ⟨ofResolutions (Classical.arbitrary _) (Classical.arbitrary _) hS⟩

end SimplicialHorseshoe

/-! ### Tensoring with a degreewise flat simplicial module, and `Tor` -/

section Tensor

open StacksDraft.SimplicialTensor MonoidalCategory

variable {A : Type u} [CommRing A]

/-- **Tensoring with a degreewise flat simplicial module preserves acyclicity.** If `M` is a
degreewise flat simplicial module and the Moore complex of `K` is acyclic, then so is the Moore
complex of the degreewise tensor product `M ⊗ K`. The proof covers `K` by its reduced décalage,
which stays null-homotopic after tensoring with `M`, and inducts on the degree along the kernel
of the covering, which is again acyclic. -/
theorem isZero_homology_tensor_of_acyclic (M : SimplicialObject (ModuleCat.{u} A))
    (hM : ∀ n, Module.Flat A (M.obj n)) (n : ℕ) :
    ∀ K : SimplicialObject (ModuleCat.{u} A),
      (∀ i, IsZero (((alternatingFaceMapComplex (ModuleCat.{u} A)).obj K).homology i)) →
      IsZero (((alternatingFaceMapComplex (ModuleCat.{u} A)).obj (M ⊗ K)).homology n) := by
  induction n with
  | zero =>
    intro K hK
    have hq := decRedδ₀_app_surjective K (hK 0)
    have hSM := shortExact_tensor_simpKer M hM (decRedδ₀ K) (fun n => hq n.unop.len)
    have : Epi (HomologicalComplex.homologyMap
        ((alternatingFaceMapComplex (ModuleCat.{u} A)).map (M ◁ decRedδ₀ K)) 0) :=
      ShortComplex.HorseshoeAux.epi_homologyMap_g_zero hSM
    exact IsZero.of_epi (HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex (ModuleCat.{u} A)).map (M ◁ decRedδ₀ K)) 0)
      (isZero_homology_tensor_decRed K M 0)
  | succ n ih =>
    intro K hK
    have hq := decRedδ₀_app_surjective K (hK 0)
    have hSM := shortExact_tensor_simpKer M hM (decRedδ₀ K) (fun n => hq n.unop.len)
    have hSN := shortExact_map_alternatingFaceMapComplex_of_linear
      (T := ShortComplex.mk (simpKerι (decRedδ₀ K)) (decRedδ₀ K) (simpKerι_comp _))
      (fun n => LinearMap.exact_subtype_ker_map ((decRedδ₀ K).app n).hom)
      (fun n => (LinearMap.ker ((decRedδ₀ K).app n).hom).injective_subtype)
      (fun n => hq n.unop.len)
    have hW : ∀ i, IsZero (((alternatingFaceMapComplex (ModuleCat.{u} A)).obj
        (simpKer (decRedδ₀ K))).homology i) := fun i =>
      (hK (i + 1)).of_iso (hSN.δIso (i + 1) i (by simp) (isZero_homology_decRed K (i + 1))
        (isZero_homology_decRed K i)).symm
    exact (ih _ hW).of_iso (hSM.δIso (n + 1) n (by simp)
      (isZero_homology_tensor_decRed K M (n + 1)) (isZero_homology_tensor_decRed K M n))

variable {M N : ModuleCat.{u} A}

/-- The terms of a simplicial projective resolution of a module are flat. -/
lemma SimplicialProjectiveResolution.flat (P : SimplicialProjectiveResolution M)
    (n : SimplexCategoryᵒᵖ) : Module.Flat A (P.obj.obj n) := by
  have : Projective (P.obj.obj n) := P.projective n.unop.len
  exact Module.Flat.of_projective

/-- For simplicial projective resolutions `P` of `M` and `Q` of `N`, the augmentation of `Q`
induces a quasi-isomorphism of Moore complexes `P ⊗ Q ⟶ P ⊗ N`. -/
instance SimplicialProjectiveResolution.quasiIso_whiskerLeft_toConst
    (P : SimplicialProjectiveResolution M) (Q : SimplicialProjectiveResolution N) :
    QuasiIso ((alternatingFaceMapComplex (ModuleCat.{u} A)).map (P.obj ◁ Q.toConst)) := by
  have hsurj : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (Q.toConst.app n).hom := fun n =>
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  have hSN := shortExact_map_alternatingFaceMapComplex_of_linear
    (T := ShortComplex.mk (simpKerι Q.toConst) Q.toConst (simpKerι_comp _))
    (fun n => LinearMap.exact_subtype_ker_map (Q.toConst.app n).hom)
    (fun n => (LinearMap.ker (Q.toConst.app n).hom).injective_subtype) hsurj
  have hK := hSN.acyclic_X₁ (by
    change QuasiIso ((alternatingFaceMapComplex (ModuleCat.{u} A)).map Q.toConst)
    infer_instance)
  exact (shortExact_tensor_simpKer P.obj P.flat Q.toConst hsurj).quasiIso_g_of_acyclic_X₁
    fun i => (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (isZero_homology_tensor_of_acyclic P.obj P.flat i _ fun j => (hK j).isZero_homology)

/-- The degreewise tensor product of a simplicial module `P` with the constant simplicial module
on `N` is `P` followed by `- ⊗ N`. -/
def tensorConstIso (P : SimplicialObject (ModuleCat.{u} A)) (N : ModuleCat.{u} A) :
    P ⊗ (SimplicialObject.const _).obj N ≅
      ((SimplicialObject.whiskering _ _).obj (tensorRight N)).obj P :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => rfl

/-- The homology of the Moore complex of `P ⊗ N` is the homology of `s(P) ⊗ N`. -/
def homologyTensorConstIso (P : SimplicialObject (ModuleCat.{u} A)) (N : ModuleCat.{u} A)
    (i : ℕ) :
    ((alternatingFaceMapComplex _).obj (P ⊗ (SimplicialObject.const _).obj N)).homology i ≅
      (((tensorRight N).mapHomologicalComplex _).obj
        ((alternatingFaceMapComplex _).obj P)).homology i :=
  (HomologicalComplex.homologyFunctor _ _ i).mapIso
    ((alternatingFaceMapComplex _).mapIso (tensorConstIso P N) ≪≫
      eqToIso (Functor.congr_obj (map_alternatingFaceMapComplex (tensorRight N)) P).symm)

/-- **The degreewise tensor product of two resolutions computes `Tor`.** For simplicial
projective resolutions `P` of `M` and `Q` of `N`, the homology of the Moore complex of the
degreewise tensor product `P ⊗ Q` is `Tor_i(M, N)`: the augmentation of `Q` gives a
quasi-isomorphism `P ⊗ Q ⟶ P ⊗ N`, and `P ⊗ N` has the homology of `N(P) ⊗ N`, where `N(P)` is
a projective resolution of `M`. -/
def SimplicialProjectiveResolution.homologyTensorIsoTor (P : SimplicialProjectiveResolution M)
    (Q : SimplicialProjectiveResolution N) (i : ℕ) :
    ((alternatingFaceMapComplex (ModuleCat.{u} A)).obj (P.obj ⊗ Q.obj)).homology i ≅
      ((Tor' (ModuleCat.{u} A) i).obj M).obj N :=
  isoOfQuasiIsoAt ((alternatingFaceMapComplex (ModuleCat.{u} A)).map (P.obj ◁ Q.toConst)) i ≪≫
    homologyTensorConstIso P.obj N i ≪≫
    (((tensorRight N).mapHomotopyEquiv
      AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
        ).toHomologyIso i).symm ≪≫
    (P.normalized.isoLeftDerivedObj (tensorRight N) i).symm

end Tensor

/-! ### The four exact sequences of the exterior square of a simplicial horseshoe -/

namespace DerivedSquare

open ExteriorSquare MonoidalCategory

variable {A : Type u} [CommRing A] {S : ShortComplex (ModuleCat.{u} A)}
  (H : SimplicialHorseshoe S)

/-- The simplicial module `Fil ⊆ Λ²P₂`, spanned in each degree by the wedges `f(p₁) ∧ p₂`. -/
abbrev filtration : SimplicialObject (ModuleCat.{u} A) := filtrationFunctor H.f

/-- The degreewise tensor product `P₁ ⊗ P₃`. -/
abbrev cross : SimplicialObject (ModuleCat.{u} A) := H.P₁.obj ⊗ H.P₃.obj

/-- The map `Λ²P₁ ⟶ Fil`, degreewise `⋀² f`. -/
def wedgeι : H.P₁.obj ⋙ exteriorSquare A ⟶ filtration H :=
  (ExteriorSquare.filtrationShortComplex H.ses H.isSplitMono_f_app).f

/-- The map `Fil ⟶ P₁ ⊗ P₃`, degreewise `f(p₁) ∧ p₂ ↦ p₁ ⊗ g(p₂)`. -/
def toCross : filtration H ⟶ cross H :=
  (ExteriorSquare.filtrationShortComplex H.ses H.isSplitMono_f_app).g

/-- The inclusion `Fil ⟶ Λ²P₂`. -/
def filtrationι : filtration H ⟶ H.P₂.obj ⋙ exteriorSquare A :=
  (ExteriorSquare.exteriorSquareShortComplex H.ses).f

/-- The composite `Λ²P₁ ⟶ Fil ⟶ P₁ ⊗ P₃` is zero. -/
@[reassoc (attr := simp)]
lemma wedgeι_comp_toCross : wedgeι H ≫ toCross H = 0 :=
  (ExteriorSquare.filtrationShortComplex H.ses H.isSplitMono_f_app).zero

/-- The composite `Fil ⟶ Λ²P₂ ⟶ Λ²P₃` is zero. -/
@[reassoc (attr := simp)]
lemma filtrationι_comp_whiskerRight :
    filtrationι H ≫ Functor.whiskerRight H.g (exteriorSquare A) = 0 :=
  (ExteriorSquare.exteriorSquareShortComplex H.ses).zero

/-- The sequence `0 → Λ²P₁ → Fil → P₁ ⊗ P₃ → 0`. -/
abbrev filtrationSequence : ShortComplex (SimplicialObject (ModuleCat.{u} A)) :=
  ShortComplex.mk _ _ (wedgeι_comp_toCross H)

/-- The sequence `0 → Fil → Λ²P₂ → Λ²P₃ → 0`. -/
abbrev exteriorSquareSequence : ShortComplex (SimplicialObject (ModuleCat.{u} A)) :=
  ShortComplex.mk _ _ (filtrationι_comp_whiskerRight H)

/-- `0 → Λ²P₁ → Fil → P₁ ⊗ P₃ → 0` is short exact. -/
theorem filtrationSequence_shortExact : (filtrationSequence H).ShortExact :=
  ExteriorSquare.filtrationShortComplex_shortExact _ (fun j => (H.shortExact_app j).exact)
    H.epi_g_app H.isSplitMono_f_app

/-- `0 → Fil → Λ²P₂ → Λ²P₃ → 0` is short exact. -/
theorem exteriorSquareSequence_shortExact : (exteriorSquareSequence H).ShortExact :=
  ExteriorSquare.exteriorSquareShortComplex_shortExact _ (fun j => (H.shortExact_app j).exact)
    H.epi_g_app

/-- The map `Λ²P₁ ⟶ Fil` is a monomorphism. -/
instance : Mono (wedgeι H) := (filtrationSequence_shortExact H).mono_f

/-- The inclusion `Fil ⟶ Λ²P₂` is a monomorphism. -/
instance : Mono (filtrationι H) := (exteriorSquareSequence_shortExact H).mono_f

/-- The composite `Λ²P₁ ⟶ Fil ⟶ Λ²P₂` is `Λ²` applied to `P₁ ⟶ P₂`. -/
@[reassoc (attr := simp)]
theorem wedgeι_comp_filtrationι :
    wedgeι H ≫ filtrationι H = Functor.whiskerRight H.f (exteriorSquare A) := by
  ext n : 2
  exact subtype_comp_toFiltration (H.f.app n).hom

/-- The quotient `Λ²P₂ / Λ²P₁`. Its Moore complex is quasi-isomorphic to the cone of the
degreewise injective map `Λ²P₁ ⟶ Λ²P₂`. -/
abbrev quotient : SimplicialObject (ModuleCat.{u} A) := cokernel (wedgeι H ≫ filtrationι H)

/-- The sequence `0 → Λ²P₁ → Λ²P₂ → Λ²P₂/Λ²P₁ → 0`. -/
abbrev quotientSequence : ShortComplex (SimplicialObject (ModuleCat.{u} A)) :=
  ShortComplex.mk (Functor.whiskerRight H.f (exteriorSquare A))
    (cokernel.π (wedgeι H ≫ filtrationι H)) (by
      rw [← wedgeι_comp_filtrationι, cokernel.condition])

/-- `0 → Λ²P₁ → Λ²P₂ → Λ²P₂/Λ²P₁ → 0` is short exact. -/
theorem quotientSequence_shortExact : (quotientSequence H).ShortExact := by
  have e : ShortComplex.mk _ _ (cokernel.condition (wedgeι H ≫ filtrationι H)) ≅
      quotientSequence H :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
  exact ShortComplex.shortExact_of_iso e
    (ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance)

/-- The cokernel of `Λ²P₁ ⟶ Fil` is `P₁ ⊗ P₃`. -/
def cokernelWedgeιIso : cokernel (wedgeι H) ≅ cross H :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
    (filtrationSequence_shortExact H).gIsCokernel

/-- The projection onto the cokernel of `Λ²P₁ ⟶ Fil`, followed by `cokernelWedgeιIso H`, is
`toCross H`. -/
@[reassoc (attr := simp)]
lemma π_comp_cokernelWedgeιIso_hom :
    cokernel.π (wedgeι H) ≫ (cokernelWedgeιIso H).hom = toCross H :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
    (filtrationSequence_shortExact H).gIsCokernel WalkingParallelPair.one

/-- The cokernel of `Fil ⟶ Λ²P₂` is `Λ²P₃`. -/
def cokernelFiltrationιIso : cokernel (filtrationι H) ≅ H.P₃.obj ⋙ exteriorSquare A :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
    (exteriorSquareSequence_shortExact H).gIsCokernel

/-- The projection onto the cokernel of `Fil ⟶ Λ²P₂`, followed by `cokernelFiltrationιIso H`, is
the map `Λ²P₂ ⟶ Λ²P₃`. -/
@[reassoc (attr := simp)]
lemma π_comp_cokernelFiltrationιIso_hom :
    cokernel.π (filtrationι H) ≫ (cokernelFiltrationιIso H).hom =
      Functor.whiskerRight H.g (exteriorSquare A) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _)
    (exteriorSquareSequence_shortExact H).gIsCokernel WalkingParallelPair.one

/-- The map `P₁ ⊗ P₃ ⟶ Λ²P₂/Λ²P₁`, induced by `Fil ⟶ Λ²P₂`. -/
def crossToQuotient : cross H ⟶ quotient H :=
  (cokernelWedgeιIso H).inv ≫ Stacks.Abelian.cokernelCompι (wedgeι H) (filtrationι H)

/-- The map `Λ²P₂/Λ²P₁ ⟶ Λ²P₃`, induced by `Λ²P₂ ⟶ Λ²P₃`. -/
def quotientToExteriorSquare : quotient H ⟶ H.P₃.obj ⋙ exteriorSquare A :=
  Stacks.Abelian.cokernelCompπ (wedgeι H) (filtrationι H) ≫ (cokernelFiltrationιIso H).hom

/-- The composite `Fil ⟶ P₁ ⊗ P₃ ⟶ Λ²P₂/Λ²P₁` is the inclusion `Fil ⟶ Λ²P₂` followed by the
projection onto `Λ²P₂/Λ²P₁`. -/
@[reassoc (attr := simp)]
lemma toCross_comp_crossToQuotient :
    toCross H ≫ crossToQuotient H = filtrationι H ≫ cokernel.π (wedgeι H ≫ filtrationι H) := by
  rw [crossToQuotient, ← π_comp_cokernelWedgeιIso_hom, Category.assoc, Iso.hom_inv_id_assoc,
    Stacks.Abelian.π_comp_cokernelCompι]

/-- The composite `Λ²P₂ ⟶ Λ²P₂/Λ²P₁ ⟶ Λ²P₃` is the map `Λ²P₂ ⟶ Λ²P₃`. -/
@[reassoc (attr := simp)]
lemma π_comp_quotientToExteriorSquare :
    cokernel.π (wedgeι H ≫ filtrationι H) ≫ quotientToExteriorSquare H =
      Functor.whiskerRight H.g (exteriorSquare A) := by
  rw [quotientToExteriorSquare, Stacks.Abelian.π_comp_cokernelCompπ_assoc,
    π_comp_cokernelFiltrationιIso_hom]

/-- The composite `P₁ ⊗ P₃ ⟶ Λ²P₂/Λ²P₁ ⟶ Λ²P₃` is zero. -/
@[reassoc (attr := simp)]
lemma crossToQuotient_comp_quotientToExteriorSquare :
    crossToQuotient H ≫ quotientToExteriorSquare H = 0 := by
  rw [crossToQuotient, quotientToExteriorSquare, Category.assoc,
    ← Category.assoc (Stacks.Abelian.cokernelCompι _ _),
    Stacks.Abelian.cokernelCompι_comp_cokernelCompπ, Limits.zero_comp, Limits.comp_zero]

/-- The sequence `0 → P₁ ⊗ P₃ → Λ²P₂/Λ²P₁ → Λ²P₃ → 0`. -/
abbrev crossSequence : ShortComplex (SimplicialObject (ModuleCat.{u} A)) :=
  ShortComplex.mk _ _ (crossToQuotient_comp_quotientToExteriorSquare H)

/-- `0 → P₁ ⊗ P₃ → Λ²P₂/Λ²P₁ → Λ²P₃ → 0` is short exact, by the third isomorphism theorem
for `Λ²P₁ ⊆ Fil ⊆ Λ²P₂`. -/
theorem crossSequence_shortExact : (crossSequence H).ShortExact := by
  refine ShortComplex.shortExact_of_iso ?_
    (Stacks.Abelian.cokernelCompShortComplex_shortExact (wedgeι H) (filtrationι H))
  exact ShortComplex.isoMk (cokernelWedgeιIso H) (Iso.refl _) (cokernelFiltrationιIso H)
    (by simp [crossToQuotient]) (by simp [quotientToExteriorSquare])

/-- The Moore complex of `Fil`. -/
abbrev filtrationComplex : ChainComplex (ModuleCat.{u} A) ℕ :=
  (alternatingFaceMapComplex (ModuleCat.{u} A)).obj (filtration H)

/-- The Moore complex of `P₁ ⊗ P₃`. -/
abbrev crossComplex : ChainComplex (ModuleCat.{u} A) ℕ :=
  (alternatingFaceMapComplex (ModuleCat.{u} A)).obj (cross H)

/-- The Moore complex of `Λ²P₂/Λ²P₁`. -/
abbrev quotientComplex : ChainComplex (ModuleCat.{u} A) ℕ :=
  (alternatingFaceMapComplex (ModuleCat.{u} A)).obj (quotient H)

/-- The homology maps of the Moore complexes of two composable maps of a short complex of
simplicial modules compose to zero. -/
private lemma homologyMap_map_comp_homologyMap_map
    (T : ShortComplex (SimplicialObject (ModuleCat.{u} A))) (i : ℕ) :
    HomologicalComplex.homologyMap ((alternatingFaceMapComplex (ModuleCat.{u} A)).map T.f) i ≫
      HomologicalComplex.homologyMap ((alternatingFaceMapComplex (ModuleCat.{u} A)).map T.g)
        i = 0 := by
  rw [← HomologicalComplex.homologyMap_comp, ← Functor.map_comp, T.zero, Functor.map_zero,
    HomologicalComplex.homologyMap_zero]

/-- The connecting morphism of the long exact sequence
`… → H_{i+1}(P₁ ⊗ P₃) → L_iΛ²(P₁) → H_i(Fil) → H_i(P₁ ⊗ P₃) → …`. -/
def filtrationδ (i : ℕ) : (crossComplex H).homology (i + 1) ⟶ homology H.P₁ i :=
  ((filtrationSequence_shortExact H).map_alternatingFaceMapComplex).δ (i + 1) i (by simp)

/-- In the long exact sequence
`… → H_{i+1}(P₁ ⊗ P₃) → L_iΛ²(P₁) → H_i(Fil) → H_i(P₁ ⊗ P₃) → …`,
two consecutive maps compose to zero. -/
@[reassoc (attr := simp)]
lemma filtration_homologyMap_comp_homologyMap (i : ℕ) :
    HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
        (wedgeι H)) i ≫
      HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
        (toCross H)) i = 0 :=
  homologyMap_map_comp_homologyMap_map (filtrationSequence H) i

/-- In the long exact sequence
`… → H_{i+1}(P₁ ⊗ P₃) → L_iΛ²(P₁) → H_i(Fil) → H_i(P₁ ⊗ P₃) → …`,
two consecutive maps compose to zero. -/
@[reassoc (attr := simp)]
lemma filtration_homologyMap_comp_δ (i : ℕ) :
    HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
        (toCross H)) (i + 1) ≫
      filtrationδ H i = 0 :=
  ((filtrationSequence_shortExact H).map_alternatingFaceMapComplex).comp_δ (i + 1) i (by simp)

/-- In the long exact sequence
`… → H_{i+1}(P₁ ⊗ P₃) → L_iΛ²(P₁) → H_i(Fil) → H_i(P₁ ⊗ P₃) → …`,
two consecutive maps compose to zero. -/
@[reassoc (attr := simp)]
lemma filtrationδ_comp_homologyMap (i : ℕ) :
    filtrationδ H i ≫ HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
        (wedgeι H)) i = 0 :=
  ((filtrationSequence_shortExact H).map_alternatingFaceMapComplex).δ_comp (i + 1) i (by simp)

/-- Exactness of the long exact sequence
`… → H_{i+1}(P₁ ⊗ P₃) → L_iΛ²(P₁) → H_i(Fil) → H_i(P₁ ⊗ P₃) → …`
at its middle terms. -/
theorem exact_filtration_middle (i : ℕ) :
    (ShortComplex.mk _ _ (filtration_homologyMap_comp_homologyMap H i)).Exact :=
  ((filtrationSequence_shortExact H).map_alternatingFaceMapComplex).homology_exact₂ i

/-- Exactness of the long exact sequence
`… → H_{i+1}(P₁ ⊗ P₃) → L_iΛ²(P₁) → H_i(Fil) → H_i(P₁ ⊗ P₃) → …`
at the target of the connecting morphism. -/
theorem exact_filtration_right (i : ℕ) :
    (ShortComplex.mk _ _ (filtration_homologyMap_comp_δ H i)).Exact :=
  ((filtrationSequence_shortExact H).map_alternatingFaceMapComplex).homology_exact₃
    (i + 1) i (by simp)

/-- Exactness of the long exact sequence
`… → H_{i+1}(P₁ ⊗ P₃) → L_iΛ²(P₁) → H_i(Fil) → H_i(P₁ ⊗ P₃) → …`
at the source of the connecting morphism. -/
theorem exact_filtration_left (i : ℕ) :
    (ShortComplex.mk _ _ (filtrationδ_comp_homologyMap H i)).Exact :=
  ((filtrationSequence_shortExact H).map_alternatingFaceMapComplex).homology_exact₁
    (i + 1) i (by simp)

/-- The connecting morphism of the long exact sequence
`… → L_{i+1}Λ²(P₃) → H_i(Fil) → L_iΛ²(P₂) → L_iΛ²(P₃) → …`. -/
def exteriorSquareδ (i : ℕ) : homology H.P₃ (i + 1) ⟶ (filtrationComplex H).homology i :=
  ((exteriorSquareSequence_shortExact H).map_alternatingFaceMapComplex).δ (i + 1) i (by simp)

/-- In the long exact sequence
`… → L_{i+1}Λ²(P₃) → H_i(Fil) → L_iΛ²(P₂) → L_iΛ²(P₃) → …`,
two consecutive maps compose to zero. -/
@[reassoc (attr := simp)]
lemma exteriorSquare_homologyMap_comp_homologyMap (i : ℕ) :
    HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
        (filtrationι H)) i ≫
      HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
        (Functor.whiskerRight H.g (exteriorSquare A))) i = 0 :=
  homologyMap_map_comp_homologyMap_map (exteriorSquareSequence H) i

/-- In the long exact sequence
`… → L_{i+1}Λ²(P₃) → H_i(Fil) → L_iΛ²(P₂) → L_iΛ²(P₃) → …`,
two consecutive maps compose to zero. -/
@[reassoc (attr := simp)]
lemma exteriorSquare_homologyMap_comp_δ (i : ℕ) :
    HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
        (Functor.whiskerRight H.g (exteriorSquare A))) (i + 1) ≫
      exteriorSquareδ H i = 0 :=
  ((exteriorSquareSequence_shortExact H).map_alternatingFaceMapComplex).comp_δ (i + 1) i (by simp)

/-- In the long exact sequence
`… → L_{i+1}Λ²(P₃) → H_i(Fil) → L_iΛ²(P₂) → L_iΛ²(P₃) → …`,
two consecutive maps compose to zero. -/
@[reassoc (attr := simp)]
lemma exteriorSquareδ_comp_homologyMap (i : ℕ) :
    exteriorSquareδ H i ≫ HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
        (filtrationι H)) i = 0 :=
  ((exteriorSquareSequence_shortExact H).map_alternatingFaceMapComplex).δ_comp (i + 1) i (by simp)

/-- Exactness of the long exact sequence
`… → L_{i+1}Λ²(P₃) → H_i(Fil) → L_iΛ²(P₂) → L_iΛ²(P₃) → …`
at its middle terms. -/
theorem exact_exteriorSquare_middle (i : ℕ) :
    (ShortComplex.mk _ _ (exteriorSquare_homologyMap_comp_homologyMap H i)).Exact :=
  ((exteriorSquareSequence_shortExact H).map_alternatingFaceMapComplex).homology_exact₂ i

/-- Exactness of the long exact sequence
`… → L_{i+1}Λ²(P₃) → H_i(Fil) → L_iΛ²(P₂) → L_iΛ²(P₃) → …`
at the target of the connecting morphism. -/
theorem exact_exteriorSquare_right (i : ℕ) :
    (ShortComplex.mk _ _ (exteriorSquare_homologyMap_comp_δ H i)).Exact :=
  ((exteriorSquareSequence_shortExact H).map_alternatingFaceMapComplex).homology_exact₃
    (i + 1) i (by simp)

/-- Exactness of the long exact sequence
`… → L_{i+1}Λ²(P₃) → H_i(Fil) → L_iΛ²(P₂) → L_iΛ²(P₃) → …`
at the source of the connecting morphism. -/
theorem exact_exteriorSquare_left (i : ℕ) :
    (ShortComplex.mk _ _ (exteriorSquareδ_comp_homologyMap H i)).Exact :=
  ((exteriorSquareSequence_shortExact H).map_alternatingFaceMapComplex).homology_exact₁
    (i + 1) i (by simp)

/-- The connecting morphism of the long exact sequence
`… → H_{i+1}(Λ²P₂/Λ²P₁) → L_iΛ²(P₁) → L_iΛ²(P₂) → H_i(Λ²P₂/Λ²P₁) → …`. -/
def quotientδ (i : ℕ) : (quotientComplex H).homology (i + 1) ⟶ homology H.P₁ i :=
  ((quotientSequence_shortExact H).map_alternatingFaceMapComplex).δ (i + 1) i (by simp)

/-- In the long exact sequence
`… → H_{i+1}(Λ²P₂/Λ²P₁) → L_iΛ²(P₁) → L_iΛ²(P₂) → H_i(Λ²P₂/Λ²P₁) → …`,
two consecutive maps compose to zero. -/
@[reassoc (attr := simp)]
lemma quotient_homologyMap_comp_homologyMap (i : ℕ) :
    HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
        (Functor.whiskerRight H.f (exteriorSquare A))) i ≫
      HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
        (cokernel.π (wedgeι H ≫ filtrationι H))) i = 0 :=
  homologyMap_map_comp_homologyMap_map (quotientSequence H) i

/-- In the long exact sequence
`… → H_{i+1}(Λ²P₂/Λ²P₁) → L_iΛ²(P₁) → L_iΛ²(P₂) → H_i(Λ²P₂/Λ²P₁) → …`,
two consecutive maps compose to zero. -/
@[reassoc (attr := simp)]
lemma quotient_homologyMap_comp_δ (i : ℕ) :
    HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
        (cokernel.π (wedgeι H ≫ filtrationι H))) (i + 1) ≫
      quotientδ H i = 0 :=
  ((quotientSequence_shortExact H).map_alternatingFaceMapComplex).comp_δ (i + 1) i (by simp)

/-- In the long exact sequence
`… → H_{i+1}(Λ²P₂/Λ²P₁) → L_iΛ²(P₁) → L_iΛ²(P₂) → H_i(Λ²P₂/Λ²P₁) → …`,
two consecutive maps compose to zero. -/
@[reassoc (attr := simp)]
lemma quotientδ_comp_homologyMap (i : ℕ) :
    quotientδ H i ≫ HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
        (Functor.whiskerRight H.f (exteriorSquare A))) i = 0 :=
  ((quotientSequence_shortExact H).map_alternatingFaceMapComplex).δ_comp (i + 1) i (by simp)

/-- Exactness of the long exact sequence
`… → H_{i+1}(Λ²P₂/Λ²P₁) → L_iΛ²(P₁) → L_iΛ²(P₂) → H_i(Λ²P₂/Λ²P₁) → …`
at its middle terms. -/
theorem exact_quotient_middle (i : ℕ) :
    (ShortComplex.mk _ _ (quotient_homologyMap_comp_homologyMap H i)).Exact :=
  ((quotientSequence_shortExact H).map_alternatingFaceMapComplex).homology_exact₂ i

/-- Exactness of the long exact sequence
`… → H_{i+1}(Λ²P₂/Λ²P₁) → L_iΛ²(P₁) → L_iΛ²(P₂) → H_i(Λ²P₂/Λ²P₁) → …`
at the target of the connecting morphism. -/
theorem exact_quotient_right (i : ℕ) :
    (ShortComplex.mk _ _ (quotient_homologyMap_comp_δ H i)).Exact :=
  ((quotientSequence_shortExact H).map_alternatingFaceMapComplex).homology_exact₃
    (i + 1) i (by simp)

/-- Exactness of the long exact sequence
`… → H_{i+1}(Λ²P₂/Λ²P₁) → L_iΛ²(P₁) → L_iΛ²(P₂) → H_i(Λ²P₂/Λ²P₁) → …`
at the source of the connecting morphism. -/
theorem exact_quotient_left (i : ℕ) :
    (ShortComplex.mk _ _ (quotientδ_comp_homologyMap H i)).Exact :=
  ((quotientSequence_shortExact H).map_alternatingFaceMapComplex).homology_exact₁
    (i + 1) i (by simp)

/-- The connecting morphism of the long exact sequence
`… → L_{i+1}Λ²(P₃) → H_i(P₁ ⊗ P₃) → H_i(Λ²P₂/Λ²P₁) → L_iΛ²(P₃) → …`. -/
def crossδ (i : ℕ) : homology H.P₃ (i + 1) ⟶ (crossComplex H).homology i :=
  ((crossSequence_shortExact H).map_alternatingFaceMapComplex).δ (i + 1) i (by simp)

/-- In the long exact sequence
`… → L_{i+1}Λ²(P₃) → H_i(P₁ ⊗ P₃) → H_i(Λ²P₂/Λ²P₁) → L_iΛ²(P₃) → …`,
two consecutive maps compose to zero. -/
@[reassoc (attr := simp)]
lemma cross_homologyMap_comp_homologyMap (i : ℕ) :
    HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
        (crossToQuotient H)) i ≫
      HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
        (quotientToExteriorSquare H)) i = 0 :=
  homologyMap_map_comp_homologyMap_map (crossSequence H) i

/-- In the long exact sequence
`… → L_{i+1}Λ²(P₃) → H_i(P₁ ⊗ P₃) → H_i(Λ²P₂/Λ²P₁) → L_iΛ²(P₃) → …`,
two consecutive maps compose to zero. -/
@[reassoc (attr := simp)]
lemma cross_homologyMap_comp_δ (i : ℕ) :
    HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
        (quotientToExteriorSquare H)) (i + 1) ≫
      crossδ H i = 0 :=
  ((crossSequence_shortExact H).map_alternatingFaceMapComplex).comp_δ (i + 1) i (by simp)

/-- In the long exact sequence
`… → L_{i+1}Λ²(P₃) → H_i(P₁ ⊗ P₃) → H_i(Λ²P₂/Λ²P₁) → L_iΛ²(P₃) → …`,
two consecutive maps compose to zero. -/
@[reassoc (attr := simp)]
lemma crossδ_comp_homologyMap (i : ℕ) :
    crossδ H i ≫ HomologicalComplex.homologyMap
      ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
        (crossToQuotient H)) i = 0 :=
  ((crossSequence_shortExact H).map_alternatingFaceMapComplex).δ_comp (i + 1) i (by simp)

/-- Exactness of the long exact sequence
`… → L_{i+1}Λ²(P₃) → H_i(P₁ ⊗ P₃) → H_i(Λ²P₂/Λ²P₁) → L_iΛ²(P₃) → …`
at its middle terms. -/
theorem exact_cross_middle (i : ℕ) :
    (ShortComplex.mk _ _ (cross_homologyMap_comp_homologyMap H i)).Exact :=
  ((crossSequence_shortExact H).map_alternatingFaceMapComplex).homology_exact₂ i

/-- Exactness of the long exact sequence
`… → L_{i+1}Λ²(P₃) → H_i(P₁ ⊗ P₃) → H_i(Λ²P₂/Λ²P₁) → L_iΛ²(P₃) → …`
at the target of the connecting morphism. -/
theorem exact_cross_right (i : ℕ) :
    (ShortComplex.mk _ _ (cross_homologyMap_comp_δ H i)).Exact :=
  ((crossSequence_shortExact H).map_alternatingFaceMapComplex).homology_exact₃
    (i + 1) i (by simp)

/-- Exactness of the long exact sequence
`… → L_{i+1}Λ²(P₃) → H_i(P₁ ⊗ P₃) → H_i(Λ²P₂/Λ²P₁) → L_iΛ²(P₃) → …`
at the source of the connecting morphism. -/
theorem exact_cross_left (i : ℕ) :
    (ShortComplex.mk _ _ (crossδ_comp_homologyMap H i)).Exact :=
  ((crossSequence_shortExact H).map_alternatingFaceMapComplex).homology_exact₁
    (i + 1) i (by simp)

/-- In the long exact sequences, the map `L_iΛ²(P₁) → H_i(Fil) → L_iΛ²(P₂)` is the map induced
by `S.f` on derived exterior squares. -/
theorem homologyMap_wedgeι_comp_homologyMap_filtrationι (i : ℕ) :
    HomologicalComplex.homologyMap ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
        (wedgeι H)) i ≫
      HomologicalComplex.homologyMap ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
        (filtrationι H)) i =
      SimplicialProjectiveResolution.derivedMap (exteriorSquare A) S.f H.P₁ H.P₂ i := by
  rw [← HomologicalComplex.homologyMap_comp, ← Functor.map_comp, wedgeι_comp_filtrationι,
    H.isLift_f.derivedMap_eq]

/-- The map `L_iΛ²(P₁) → L_iΛ²(P₂)` of `Λ²` applied to the horseshoe is the map induced by
`S.f` on derived exterior squares. -/
theorem homologyMap_whiskerRight_f (i : ℕ) :
    HomologicalComplex.homologyMap ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
        (Functor.whiskerRight H.f (exteriorSquare A))) i =
      SimplicialProjectiveResolution.derivedMap (exteriorSquare A) S.f H.P₁ H.P₂ i :=
  (H.isLift_f.derivedMap_eq _ i).symm

/-- The map `L_iΛ²(P₂) → L_iΛ²(P₃)` of `Λ²` applied to the horseshoe is the map induced by
`S.g` on derived exterior squares. -/
theorem homologyMap_whiskerRight_g (i : ℕ) :
    HomologicalComplex.homologyMap ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
        (Functor.whiskerRight H.g (exteriorSquare A))) i =
      SimplicialProjectiveResolution.derivedMap (exteriorSquare A) S.g H.P₂ H.P₃ i :=
  (H.isLift_g.derivedMap_eq _ i).symm

/-- **The cross term is `Tor`.** For a simplicial horseshoe over `0 → M' → M → M'' → 0`, the
homology of the Moore complex of `P₁ ⊗ P₃` is `Tor_i(M', M'')`. -/
def crossHomologyIsoTor (i : ℕ) :
    (crossComplex H).homology i ≅ ((Tor' (ModuleCat.{u} A) i).obj S.X₁).obj S.X₃ :=
  SimplicialProjectiveResolution.homologyTensorIsoTor H.P₁ H.P₃ i

end DerivedSquare

/-! ### Multiplication by a ring element -/

namespace DerivedSquare

variable {A : Type u} [CommRing A] {M : ModuleCat.{u} A}

/-- **`LΛ²` of multiplication by `c` is multiplication by `c²`.** The map induced on
`L_iΛ²(M)` by `c • 𝟙 M`, computed with any two resolutions of `M`, is `c²` times the comparison
isomorphism: `c • 𝟙` lifts to `c • 𝟙` on a resolution, and `⋀²(c • id) = c² • id`. -/
theorem derivedMap_smul_id (c : A) (P Q : SimplicialProjectiveResolution M) (i : ℕ) :
    SimplicialProjectiveResolution.derivedMap (exteriorSquare A) (c • 𝟙 M) P Q i =
      c ^ 2 • (SimplicialProjectiveResolution.derivedIso (exteriorSquare A) P Q i).hom := by
  let φ : P.obj ⟶ P.obj :=
    { app n := c • 𝟙 _
      naturality _ _ _ := by simp [Linear.smul_comp, Linear.comp_smul] }
  have hφ : P.IsLift P (c • 𝟙 M) φ := by
    rw [SimplicialProjectiveResolution.isLift_iff]
    simp [φ, Linear.smul_comp, Linear.comp_smul]
  have hcx : SimplicialProjectiveResolution.derivedComplexMap (exteriorSquare A) φ =
      c ^ 2 • 𝟙 _ := by
    ext n : 1
    exact ModuleCat.hom_ext (exteriorPower.map_smul_id c 2)
  rw [← Category.comp_id (c • 𝟙 M), ← SimplicialProjectiveResolution.derivedMap_comp _ _ _ P P Q,
    hφ.derivedMap_eq, hcx, HomologicalComplex.homologyMap_smul_id_of_linear, Linear.smul_comp,
    Category.id_comp]
  rfl

/-- For a nonzerodivisor `c` on `M`, the sequence `0 → M →c M → M/cM → 0` is short exact, with
`M/cM` the cokernel of multiplication by `c`. -/
theorem smul_shortExact {c : A} (hc : IsSMulRegular M c) :
    (ShortComplex.mk (c • 𝟙 M) (cokernel.π (c • 𝟙 M)) (cokernel.condition _)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _)
    ((ModuleCat.mono_iff_injective _).2 hc) inferInstance

section Smul

variable {N : ModuleCat.{u} A} {c : A} {g : M ⟶ N} {w : (c • 𝟙 M) ≫ g = 0}
  (H : SimplicialHorseshoe (ShortComplex.mk (c • 𝟙 M) g w))

/-- In a simplicial horseshoe over `0 → M →c M → N → 0`, the map `L_iΛ²(P₁) → L_iΛ²(P₂)` between
two computations of `L_iΛ²(M)` is `c²` times the comparison isomorphism. -/
theorem homologyMap_whiskerRight_f_eq_smul (i : ℕ) :
    HomologicalComplex.homologyMap ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
        (Functor.whiskerRight H.f (exteriorSquare A))) i =
      c ^ 2 • (SimplicialProjectiveResolution.derivedIso (exteriorSquare A) H.P₁ H.P₂ i).hom :=
  (homologyMap_whiskerRight_f H i).trans (derivedMap_smul_id c H.P₁ H.P₂ i)

/-- The map `L_iΛ²(M) → H_i(Λ²P₂/Λ²P₁)`, with `L_iΛ²(M)` computed by `P₁`. -/
def toQuotientHomology (i : ℕ) : homology H.P₁ i ⟶ (quotientComplex H).homology i :=
  (SimplicialProjectiveResolution.derivedIso (exteriorSquare A) H.P₁ H.P₂ i).hom ≫
    HomologicalComplex.homologyMap ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
      (cokernel.π (wedgeι H ≫ filtrationι H))) i

/-- In a simplicial horseshoe over `0 → M →c M → N → 0`, multiplication by `c²` on `L_iΛ²(M)`
followed by the comparison isomorphism is the map `L_iΛ²(P₁) → L_iΛ²(P₂)`. -/
lemma smul_comp_derivedIso_hom (i : ℕ) :
    (c ^ 2 • 𝟙 (homology H.P₁ i)) ≫
        (SimplicialProjectiveResolution.derivedIso (exteriorSquare A) H.P₁ H.P₂ i).hom =
      HomologicalComplex.homologyMap ((alternatingFaceMapComplex (ModuleCat.{u} A)).map
        (Functor.whiskerRight H.f (exteriorSquare A))) i := by
  rw [homologyMap_whiskerRight_f_eq_smul, Linear.smul_comp, Category.id_comp]

/-- **The cone of `c²` on `LΛ²(M)`, at the middle terms.** In a simplicial horseshoe over
`0 → M →c M → N → 0`, the sequence `L_iΛ²(M) →c² L_iΛ²(M) → H_i(Λ²P₂/Λ²P₁)` is exact. -/
theorem exact_quotient_smul_middle (i : ℕ) :
    (ShortComplex.mk (c ^ 2 • 𝟙 (homology H.P₁ i)) (toQuotientHomology H i) (by
        rw [toQuotientHomology, ← Category.assoc, smul_comp_derivedIso_hom]
        exact quotient_homologyMap_comp_homologyMap H i)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (exact_quotient_middle H i)
  exact ShortComplex.isoMk (Iso.refl _)
    (SimplicialProjectiveResolution.derivedIso (exteriorSquare A) H.P₁ H.P₂ i).symm (Iso.refl _)
    (by simp [← smul_comp_derivedIso_hom H]) (by simp [toQuotientHomology])

/-- **The cone of `c²` on `LΛ²(M)`, at the target of the connecting morphism.** The sequence
`L_{i+1}Λ²(M) → H_{i+1}(Λ²P₂/Λ²P₁) → L_iΛ²(M)` is exact. -/
theorem exact_quotient_smul_right (i : ℕ) :
    (ShortComplex.mk (toQuotientHomology H (i + 1)) (quotientδ H i) (by
        rw [toQuotientHomology, Category.assoc, quotient_homologyMap_comp_δ,
          Limits.comp_zero])).Exact := by
  refine ShortComplex.exact_of_iso ?_ (exact_quotient_right H i)
  exact ShortComplex.isoMk
    (SimplicialProjectiveResolution.derivedIso (exteriorSquare A) H.P₁ H.P₂ (i + 1)).symm
    (Iso.refl _) (Iso.refl _) (by simp [toQuotientHomology]) (by simp)

/-- **The cone of `c²` on `LΛ²(M)`, at the source of the connecting morphism.** The sequence
`H_{i+1}(Λ²P₂/Λ²P₁) → L_iΛ²(M) →c² L_iΛ²(M)` is exact. -/
theorem exact_quotient_smul_left (i : ℕ) :
    (ShortComplex.mk (quotientδ H i) (c ^ 2 • 𝟙 (homology H.P₁ i)) (by
        rw [← cancel_mono (SimplicialProjectiveResolution.derivedIso (exteriorSquare A)
          H.P₁ H.P₂ i).hom, Limits.zero_comp, Category.assoc, smul_comp_derivedIso_hom]
        exact quotientδ_comp_homologyMap H i)).Exact := by
  refine ShortComplex.exact_of_iso ?_ (exact_quotient_left H i)
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (SimplicialProjectiveResolution.derivedIso (exteriorSquare A) H.P₁ H.P₂ i).symm
    (by simp) (by simp [← smul_comp_derivedIso_hom H])

end Smul

end DerivedSquare

end Stacks
