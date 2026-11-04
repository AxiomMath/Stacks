module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherenceUnique
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerMapSuccessor

/-!
# The comparison of tensor powers along a functor is multiplicative

Let `L` be an invertible sheaf of modules on a ringed site and let `R` be a functor to sheaves of
modules on a second ringed site, equipped with a tensorator `R(M ⊗ N) ≅ R M ⊗ R N` and an
identification `R 𝒪 ≅ 𝒪'` of the structure sheaves.
`Stacks.SheafOfModules.TensorPower.mapTensorPowerIso` compares the integral tensor powers,
`R(L^{⊗ n}) ≅ (R L)^{⊗ n}`. This file transports the coherent multiplication
`L^{⊗ n} ⊗ L^{⊗ m} ≅ L^{⊗ (n + m)}` along that comparison, shows that the transported family
satisfies the normalisations of a coherent multiplication, and deduces that the comparison
carries the coherent multiplication for `L` to the one for `R L`.

## Main definitions

* `Stacks.SheafOfModules.TensorPower.tensorPowerComparison`: the comparison
  `R(L^{⊗ n}) ≅ (R L)^{⊗ n}`, i.e. `mapTensorPowerIso` for the tensorator restricted to the
  second slot.
* `Stacks.SheafOfModules.TensorPower.mulIsoOfComparison`: the transported multiplication
  `(R L)^{⊗ n} ⊗ (R L)^{⊗ m} ≅ (R L)^{⊗ (n + m)}`.
* `Stacks.SheafOfModules.TensorPower.IsNaturalLeft`, `IsNaturalRight`, `IsLeftUnital`,
  `IsRightUnital`, `IsAssociative` and `IsSymmetric`: the compatibilities of the tensorator with
  the naturality, unit, associativity and symmetry constraints of the tensor product.
* `Stacks.SheafOfModules.TensorPower.tensorPowerCoherenceOfComparison`: the transported family,
  bundled as a `TensorPowerCoherence` for `R L`.

## Main results

* `Stacks.SheafOfModules.TensorPower.tensorPowerComparison_reindex`: the comparison commutes with
  reindexing along an equality of exponents.
* `Stacks.SheafOfModules.TensorPower.mulIsoOfComparison_zero_right`,
  `mulIsoOfComparison_zero_left`, `mulIsoOfComparison_one_right`, `mulIsoOfComparison_assoc` and
  `mulIsoOfComparison_comm`: the five normalisations of a coherent multiplication for the
  transported multiplication.
* `Stacks.SheafOfModules.TensorPower.mapTensorPowerIso_mul_zero_right`: the comparison carries
  the coherent multiplication in degree `(n, 0)` to the right unit constraint.
* `Stacks.SheafOfModules.TensorPower.mulIsoOfComparison_eq` and
  `map_coherentMulIso_tensorPowerComparison`: the comparison of integral tensor powers is
  multiplicative — it carries the coherent multiplication for `L` to the one for `R L`, in every
  pair of degrees.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe v u v' u' w

namespace Stacks.SheafOfModules.TensorPower

attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalCategory
  Stacks.SheafOfModules.Strict.braidedCategory

/-! ### Transfer of a unit constraint along an isomorphism -/

section Transfer

variable {M : Type u} [Category.{v} M] [MonoidalCategory M]

/-- Transfer of the right unit constraint: whiskering an isomorphism onto the unit and then
using the unit constraint is the unit constraint followed by the isomorphism. -/
@[reassoc]
public theorem whiskerLeft_rightUnitor_transfer {A B Z : M} (f : A ⟶ B) (g : Z ⟶ 𝟙_ M) :
    (A ◁ g) ≫ (ρ_ A).hom ≫ f = (f ⊗ₘ g) ≫ (ρ_ B).hom := by
  rw [tensorHom_def', Category.assoc, MonoidalCategory.rightUnitor_naturality]

/-- Transfer of the left unit constraint: whiskering a morphism into the unit on the left and
then using the unit constraint is a tensor product of morphisms followed by the unit
constraint. -/
@[reassoc]
public theorem whiskerRight_leftUnitor_transfer {A B Z : M} (f : A ⟶ B) (g : Z ⟶ 𝟙_ M) :
    (g ▷ A) ≫ (λ_ A).hom ≫ f = (g ⊗ₘ f) ≫ (λ_ B).hom := by
  rw [tensorHom_def, Category.assoc, MonoidalCategory.leftUnitor_naturality]

/-- Transfer of a factorised whiskering: whiskering a composite on the left and then whiskering
on the right splits as a tensor product of morphisms followed by the remaining whiskering. -/
@[reassoc]
public theorem whiskerLeft_whiskerRight_transfer {A B Z Z' W : M} (f : A ⟶ B) (h : Z ⟶ Z')
    (k : Z' ⟶ W) : (A ◁ (h ≫ k)) ≫ (f ▷ W) = (f ⊗ₘ h) ≫ (B ◁ k) := by
  rw [MonoidalCategory.whiskerLeft_comp, Category.assoc, whisker_exchange, tensorHom_def',
    Category.assoc]

/-- Absorbing a left whiskering into the second factor of a tensor product of morphisms. -/
@[reassoc]
public theorem whiskerLeft_comp_tensorHom {A B Z Z' W : M} (f : A ⟶ B) (x : Z ⟶ Z') (y : Z' ⟶ W) :
    (A ◁ x) ≫ (f ⊗ₘ y) = f ⊗ₘ (x ≫ y) := by
  rw [← MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
    Category.id_comp]

/-- Absorbing a right whiskering into the first factor of a tensor product of morphisms. -/
@[reassoc]
public theorem whiskerRight_comp_tensorHom {A A' B Z W : M} (x : A ⟶ A') (f : A' ⟶ B)
    (y : Z ⟶ W) : (x ▷ Z) ≫ (f ⊗ₘ y) = (x ≫ f) ⊗ₘ y := by
  rw [← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom,
    Category.id_comp]

/-- Absorbing a left whiskering after a tensor product of morphisms. -/
@[reassoc]
public theorem tensorHom_comp_whiskerLeft {A B Z Z' W : M} (f : A ⟶ B) (g : Z ⟶ Z')
    (k : Z' ⟶ W) : (f ⊗ₘ g) ≫ (B ◁ k) = f ⊗ₘ (g ≫ k) := by
  rw [← MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
    Category.comp_id]

/-- A square `b ≫ t ≫ μ = c ≫ p` with `c = c₁ ≫ s`, a square for `s ≫ p`, a naturality square
in the second slot and factorisations of `r` and `t` combine to
`(b ≫ t) ≫ μ = (b ≫ t) ≫ t₀ ≫ s'`. -/
private theorem oneRight_transfer {S A N A' N' Q S₁ S₂ L : M} {b : S ⟶ A ⊗ N}
    {t : A ⊗ N ⟶ A' ⊗ N'} {μ : A' ⊗ N' ⟶ Q} {c : S ⟶ S₂} {c₁ : S ⟶ S₁} {s : S₁ ⟶ S₂}
    {p : S₂ ⟶ Q} {b₁ : S₁ ⟶ A ⊗ L} {pₙ : A ⟶ A'} {s' : A' ⊗ L ⟶ Q} {r : N ⟶ L}
    {p₁ : N ⟶ N'} {e : N' ⟶ L} {t₀ : A' ⊗ N' ⟶ A' ⊗ L}
    (hspec : b ≫ t ≫ μ = c ≫ p) (hc : c = c₁ ≫ s) (hsucc : s ≫ p = b₁ ≫ (pₙ ▷ L) ≫ s')
    (hnat : c₁ ≫ b₁ = b ≫ (A ◁ r)) (hr : r = p₁ ≫ e) (ht : t = pₙ ⊗ₘ p₁)
    (ht₀ : t₀ = A' ◁ e) :
    (b ≫ t) ≫ μ = (b ≫ t) ≫ t₀ ≫ s' := by
  simp only [Category.assoc]
  rw [hspec, hc, Category.assoc, hsucc, reassoc_of% hnat, hr, ht, ht₀,
    whiskerLeft_whiskerRight_transfer_assoc]

/-- Two squares around a naturality square in the first slot compose to
`b ≫ (x ⊗ₘ pₖ) ≫ (μ ▷ D) ≫ μ₂ = c' ≫ c₂ ≫ p₂`. -/
private theorem assocLeft_transfer {S A B C D E A₂ S₂ Y G : M} {b : S ⟶ A ⊗ B} {x : A ⟶ C}
    {pₖ : B ⟶ D} {μ : C ⟶ E} {μ₂ : E ⊗ D ⟶ G} {c : A ⟶ A₂} {p : A₂ ⟶ E} {c' : S ⟶ S₂}
    {b₂ : S₂ ⟶ A₂ ⊗ B} {c₂ : S₂ ⟶ Y} {p₂ : Y ⟶ G}
    (h₁ : x ≫ μ = c ≫ p) (h₂ : b ≫ (c ▷ B) = c' ≫ b₂) (h₃ : b₂ ≫ (p ⊗ₘ pₖ) ≫ μ₂ = c₂ ≫ p₂) :
    b ≫ (x ⊗ₘ pₖ) ≫ (μ ▷ D) ≫ μ₂ = c' ≫ c₂ ≫ p₂ := by
  rw [tensorHom_comp_whiskerRight_assoc, h₁, ← whiskerRight_comp_tensorHom, Category.assoc,
    reassoc_of% h₂, h₃]

/-- A square for the associator, two squares around a naturality square in the second slot and a
reindexing square compose to an evaluation of the right-hand side of an associativity law. -/
private theorem assocRight_transfer {S AB A B C A' B' C' BC K NK T S' S'' X Y Y' : M}
    {b : S ⟶ AB ⊗ C} {bₙₘ : AB ⟶ A ⊗ B} {pₙ : A ⟶ A'} {pₘ : B ⟶ B'} {pₖ : C ⟶ C'}
    {μₘₖ : B' ⊗ C' ⟶ K} {μₙ : A' ⊗ K ⟶ NK} {ε : NK ⟶ T} {a : S ⟶ S'} {bₙ : S' ⟶ A ⊗ BC}
    {bₘₖ : BC ⟶ B ⊗ C} {cₘₖ : BC ⟶ X} {pₘₖ : X ⟶ K} {w : S' ⟶ S''} {bₙ' : S'' ⟶ A ⊗ X}
    {c : S'' ⟶ Y} {p : Y ⟶ NK} {r : Y ⟶ Y'} {p' : Y' ⟶ T}
    (hassoc : b ≫ (bₙₘ ▷ C) ≫ (α_ A B C).hom = a ≫ bₙ ≫ (A ◁ bₘₖ))
    (hmk : bₘₖ ≫ (pₘ ⊗ₘ pₖ) ≫ μₘₖ = cₘₖ ≫ pₘₖ) (hnat : bₙ ≫ (A ◁ cₘₖ) = w ≫ bₙ')
    (hn : bₙ' ≫ (pₙ ⊗ₘ pₘₖ) ≫ μₙ = c ≫ p) (hre : r ≫ p' = p ≫ ε) :
    b ≫ ((bₙₘ ≫ (pₙ ⊗ₘ pₘ)) ⊗ₘ pₖ) ≫ (α_ A' B' C').hom ≫ (A' ◁ μₘₖ) ≫ μₙ ≫ ε =
      a ≫ w ≫ c ≫ r ≫ p' := by
  rw [← whiskerRight_comp_tensorHom]
  simp only [Category.assoc]
  rw [MonoidalCategory.associator_naturality_assoc, reassoc_of% hassoc,
    tensorHom_comp_whiskerLeft_assoc, whiskerLeft_comp_tensorHom_assoc, hmk,
    ← whiskerLeft_comp_tensorHom]
  simp only [Category.assoc]
  rw [reassoc_of% hnat, reassoc_of% hn, hre]

/-- An associativity law follows from evaluations `hL` and `hR` of its two sides, once the tensor
products of morphisms and the associativity constraint are written in the monoidal structure. -/
private theorem assoc_transfer {S AB A B C A' B' C' E K NK G : M} {b : S ⟶ AB ⊗ C}
    {τ : AB ⊗ C ⟶ (A' ⊗ B') ⊗ C'} {bₙₘ : AB ⟶ A ⊗ B} {t : A ⊗ B ⟶ A' ⊗ B'} {pₙ : A ⟶ A'}
    {pₘ : B ⟶ B'} {pₖ : C ⟶ C'} {l : (A' ⊗ B') ⊗ C' ⟶ E ⊗ C'} {μ : A' ⊗ B' ⟶ E}
    {μ₂ : E ⊗ C' ⟶ G} {as : (A' ⊗ B') ⊗ C' ⟶ A' ⊗ (B' ⊗ C')}
    {l' : A' ⊗ (B' ⊗ C') ⟶ A' ⊗ K} {μₘₖ : B' ⊗ C' ⟶ K} {μ₃ : A' ⊗ K ⟶ NK} {ε : NK ⟶ G}
    {lhs : S ⟶ G} {rhs : S ⟶ G}
    (hτ : τ = (bₙₘ ≫ t) ⊗ₘ pₖ) (ht : t = pₙ ⊗ₘ pₘ) (hl : l = μ ▷ C')
    (has : as = (α_ A' B' C').hom) (hl' : l' = A' ◁ μₘₖ)
    (hL : b ≫ ((bₙₘ ≫ (pₙ ⊗ₘ pₘ)) ⊗ₘ pₖ) ≫ (μ ▷ C') ≫ μ₂ = lhs)
    (hR : b ≫ ((bₙₘ ≫ (pₙ ⊗ₘ pₘ)) ⊗ₘ pₖ) ≫ (α_ A' B' C').hom ≫ (A' ◁ μₘₖ) ≫ μ₃ ≫ ε = rhs)
    (h : lhs = rhs) :
    (b ≫ τ) ≫ l ≫ μ₂ = (b ≫ τ) ≫ as ≫ l' ≫ μ₃ ≫ ε := by
  simp only [Category.assoc]
  rw [hτ, ht, hl, has, hl', hL, h, hR]

/-- A commutativity law follows from the defining squares of both sides, naturality of the
symmetry constraint, a compatibility `hsym` with it, and a reindexing square. -/
private theorem comm_transfer [BraidedCategory M] {S A B A' B' Q Q' S' Y Z : M}
    {b : S ⟶ A ⊗ B} {t : A ⊗ B ⟶ A' ⊗ B'} {μ : A' ⊗ B' ⟶ Q} {c : S ⟶ Y} {p : Y ⟶ Q}
    {σ : S ⟶ S'} {c' : S' ⟶ Z} {r : Z ⟶ Y} {p' : Z ⟶ Q'} {ε : Q' ⟶ Q} {pₙ : A ⟶ A'}
    {pₘ : B ⟶ B'} {br : A' ⊗ B' ⟶ B' ⊗ A'} {b' : S' ⟶ B ⊗ A} {t' : B ⊗ A ⟶ B' ⊗ A'}
    {μ' : B' ⊗ A' ⟶ Q'}
    (hspec : b ≫ t ≫ μ = c ≫ p) (hc : c = σ ≫ c' ≫ r) (hre : r ≫ p = p' ≫ ε)
    (ht : t = pₙ ⊗ₘ pₘ) (hbr : br = (β_ A' B').hom) (hsym : σ ≫ b' = b ≫ (β_ A B).hom)
    (ht' : t' = pₘ ⊗ₘ pₙ) (hspec' : b' ≫ t' ≫ μ' = c' ≫ p') :
    (b ≫ t) ≫ μ = (b ≫ t) ≫ br ≫ μ' ≫ ε := by
  simp only [Category.assoc]
  rw [hspec, hc, Category.assoc, Category.assoc, hre, ht, hbr,
    BraidedCategory.braiding_naturality_assoc, ← reassoc_of% hsym, ← ht', reassoc_of% hspec']

end Transfer

/-- A functor carries a factorisation of a composite to a factorisation of the image of the
composite, followed by any morphism. -/
private theorem map_comp_transfer {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ] (F : 𝒜 ⥤ ℬ)
    {X Y Z X₁ X₂ X₃ : 𝒜} {W : ℬ} {f : X ⟶ Y} {g : Y ⟶ Z} {f₁ : X ⟶ X₁} {f₂ : X₁ ⟶ X₂}
    {f₃ : X₂ ⟶ X₃} {f₄ : X₃ ⟶ Z} (h : f ≫ g = f₁ ≫ f₂ ≫ f₃ ≫ f₄) (q : F.obj Z ⟶ W) :
    F.map f ≫ F.map g ≫ q = F.map f₁ ≫ F.map f₂ ≫ F.map f₃ ≫ F.map f₄ ≫ q := by
  rw [← F.map_comp_assoc, h]
  simp only [F.map_comp, Category.assoc]

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-! ### The degree-`(n, 0)` law of the chosen coherence datum, at the field spelling -/

/-- The degree-`(n, 0)` normalisation of the coherent multiplication, stated against
the right unit constraint `Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso` of the tensor product
sheaf. -/
public theorem coherentMulIso_zero_right_tensorSheaf
    (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n : ℤ) :
    coherentMulIso O hO L n 0 ≪≫ tensorPowerReindex O hO L (Int.add_zero n) =
      Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso O hO (tensorPower O hO L n) :=
  (tensorPowerCoherence O hO L).mul_zero_right n

/-- The identification of the first tensor power with `L` is the left unit constraint of the
tensor product sheaf. -/
public theorem tensorPowerOneIso_eq_tensorSheafLeftUnitor
    (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] :
    tensorPowerOneIso O hO L = Stacks.SheafOfModules.tensorSheafLeftUnitor O hO L := rfl

/-- Right tensoring by a sheaf of modules acts on an isomorphism as right whiskering. -/
public theorem tensorRightFunctor_map_iso_hom
    {A B : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (i : A ≅ B)
    (N : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).flip.obj N).map
        i.hom = i.hom ▷ N :=
  congrArg Iso.hom ((tensorSheafMapIso_refl_right_eq_map O hO i N).symm.trans
    (tensorSheafMapIso_refl_right O hO i N))

/-- The degree-`(n, 1)` normalisation of the coherent multiplication, stated against
the tensor product sheaf of an identity with the identification of the first power. -/
public theorem coherentMulIso_one_right_tensorSheaf
    (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n : ℤ) :
    coherentMulIso O hO L n 1 =
      tensorSheafMapIso O hO (Iso.refl (tensorPower O hO L n)) (tensorPowerOneIso O hO L) ≪≫
        tensorPowerSuccIso O hO L n :=
  (tensorPowerCoherence O hO L).mul_one_right n

/-- The degree-`(0, n)` normalisation of the coherent multiplication, stated against
the left unit constraint of the tensor product sheaf. -/
public theorem coherentMulIso_zero_left_tensorSheaf
    (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] (n : ℤ) :
    coherentMulIso O hO L 0 n ≪≫ tensorPowerReindex O hO L (Int.zero_add n) =
      Stacks.SheafOfModules.tensorSheafLeftUnitor O hO (tensorPower O hO L n) :=
  (tensorPowerCoherence O hO L).mul_zero_left n

/-! ### The transported multiplication -/

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (O' : Dᵒᵖ ⥤ CommRingCat.{w})
  (hO' : Presheaf.IsSheaf K (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O'))
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify K AddCommGrpCat.{w}]
  (R : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO) ⥤
    _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O' hO'))
  (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
  [IsInvertible O hO L] [IsInvertible O' hO' (R.obj L)]
  (β : ∀ M N : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO),
    R.obj ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          (M)).obj (N))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O', Presheaf.isSheaf_of_isSheaf_comp _ (O') (forget₂ CommRingCat RingCat) (hO')⟩).obj
          ((R.obj M))).obj ((R.obj N))))
  (hunit : R.obj (_root_.SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ≅
    _root_.SheafOfModules.unit
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O' hO'))

/-- The comparison `R(L^{⊗ n}) ≅ (R L)^{⊗ n}` determined by a tensorator: it is
`Stacks.SheafOfModules.TensorPower.mapTensorPowerIso` for the tensor comparison the tensorator
restricts to when its second slot is `L`. -/
public def tensorPowerComparison (n : ℤ) :
    R.obj (tensorPower O hO L n) ≅ tensorPower O' hO' (R.obj L) n :=
  mapTensorPowerIso O hO O' hO' R L (fun M ↦ β M L) hunit n

/-- In degree zero the comparison of tensor powers is the comparison of the structure sheaves. -/
public theorem tensorPowerComparison_zero :
    tensorPowerComparison O hO O' hO' R L β hunit 0 = hunit :=
  mapTensorPowerIso_zero O hO O' hO' R L (fun M ↦ β M L) hunit

/-- In degree one the comparison of tensor powers is the tensorator at the structure sheaf,
followed by the comparison of the structure sheaves tensored on the right by `R L`. -/
public theorem tensorPowerComparison_one :
    tensorPowerComparison O hO O' hO' R L β hunit 1 =
      β (_root_.SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) L ≪≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', w, w, w}
          ⟨O', Presheaf.isSheaf_of_isSheaf_comp K O' (forget₂ CommRingCat RingCat) hO'⟩).flip.obj
            (R.obj L)).mapIso hunit :=
  mapTensorPowerIso_one O hO O' hO' R L (fun M ↦ β M L) hunit

/-- The comparison of tensor powers commutes with the successor comparison, in every integer
degree. -/
@[reassoc]
public theorem map_tensorPowerSuccIso_tensorPowerComparison (n : ℤ) :
    R.map (tensorPowerSuccIso O hO L n).hom ≫
        (tensorPowerComparison O hO O' hO' R L β hunit (n + 1)).hom =
      (β (tensorPower O hO L n) L).hom ≫
        ((tensorPowerComparison O hO O' hO' R L β hunit n).hom ▷ R.obj L) ≫
          (tensorPowerSuccIso O' hO' (R.obj L) n).hom := by
  rw [← tensorRightFunctor_map_iso_hom O' hO'
    (tensorPowerComparison O hO O' hO' R L β hunit n) (R.obj L)]
  exact mapTensorPowerIso_tensorPowerSuccIso O hO O' hO' R L (fun M ↦ β M L) hunit n

/-- The comparison of tensor powers commutes with reindexing along an equality of exponents. -/
public theorem tensorPowerComparison_reindex {a b : ℤ} (h : a = b) :
    R.map (tensorPowerReindex O hO L h).hom ≫
        (tensorPowerComparison O hO O' hO' R L β hunit b).hom =
      (tensorPowerComparison O hO O' hO' R L β hunit a).hom ≫
        (tensorPowerReindex O' hO' (R.obj L) h).hom := by
  subst h
  simp

/-- The multiplication on the integral tensor powers of `R L` transported along the comparison
from the coherent multiplication for `L`. -/
public def mulIsoOfComparison (n m : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O', Presheaf.isSheaf_of_isSheaf_comp _ (O') (forget₂ CommRingCat RingCat) (hO')⟩).obj
        ((tensorPower O' hO' (R.obj L) n))).obj ((tensorPower O' hO' (R.obj L) m))) ≅
      tensorPower O' hO' (R.obj L) (n + m) :=
  (tensorSheafMapIso O' hO' (tensorPowerComparison O hO O' hO' R L β hunit n)
        (tensorPowerComparison O hO O' hO' R L β hunit m)).symm ≪≫
    (β (tensorPower O hO L n) (tensorPower O hO L m)).symm ≪≫
    R.mapIso (coherentMulIso O hO L n m) ≪≫
    tensorPowerComparison O hO O' hO' R L β hunit (n + m)

/-- The defining property of the transported multiplication: the tensorator and the comparison of
the two factors, followed by it, is the coherent multiplication followed by the comparison of the
product. -/
@[reassoc]
public theorem mulIsoOfComparison_spec (n m : ℤ) :
    (β (tensorPower O hO L n) (tensorPower O hO L m)).hom ≫
        (tensorSheafMapIso O' hO' (tensorPowerComparison O hO O' hO' R L β hunit n)
          (tensorPowerComparison O hO O' hO' R L β hunit m)).hom ≫
        (mulIsoOfComparison O hO O' hO' R L β hunit n m).hom =
      R.map (coherentMulIso O hO L n m).hom ≫
        (tensorPowerComparison O hO O' hO' R L β hunit (n + m)).hom :=
  (whisker_eq _ (Iso.hom_inv_id_assoc _ _)).trans (Iso.hom_inv_id_assoc _ _)

/-- The defining property of the transported multiplication, with the comparison of the two
factors written as a tensor product of morphisms in the strict monoidal structure. -/
@[reassoc]
public theorem mulIsoOfComparison_spec_tensorHom (n m : ℤ) :
    (β (tensorPower O hO L n) (tensorPower O hO L m)).hom ≫
        ((tensorPowerComparison O hO O' hO' R L β hunit n).hom ⊗ₘ
          (tensorPowerComparison O hO O' hO' R L β hunit m).hom) ≫
        (mulIsoOfComparison O hO O' hO' R L β hunit n m).hom =
      R.map (coherentMulIso O hO L n m).hom ≫
        (tensorPowerComparison O hO O' hO' R L β hunit (n + m)).hom := by
  rw [← tensorSheafMapIso_hom_eq]
  exact mulIsoOfComparison_spec O hO O' hO' R L β hunit n m

/-- If a coherent multiplication is a morphism `u` followed by a reindexing, the comparison carries
it to the comparison of `u` followed by the reindexing of the transported tensor powers. -/
private theorem map_comp_reindex_of_eq_comp_inv {a b : ℤ} (h : a = b)
    {X : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
    (c : X ⟶ tensorPower O hO L a) (u : X ⟶ tensorPower O hO L b)
    (hc : c = u ≫ (tensorPowerReindex O hO L h).inv) :
    R.map c ≫ (tensorPowerComparison O hO O' hO' R L β hunit a).hom ≫
        (tensorPowerReindex O' hO' (R.obj L) h).hom =
      R.map u ≫ (tensorPowerComparison O hO O' hO' R L β hunit b).hom := by
  rw [hc, R.map_comp, Category.assoc, ← tensorPowerComparison_reindex O hO O' hO' R L β hunit h,
    ← R.map_comp_assoc, ← R.map_comp_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- A unit-type normalisation of the transported multiplication follows from its image under the
comparison, written with the defining property of the transported multiplication. -/
private theorem mulIsoOfComparison_reindex_eq {n m k : ℤ} (h : n + m = k)
    (U : (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨O', Presheaf.isSheaf_of_isSheaf_comp _ (O') (forget₂ CommRingCat RingCat) (hO')⟩).obj
        ((tensorPower O' hO' (R.obj L) n))).obj ((tensorPower O' hO' (R.obj L) m))) ≅
      tensorPower O' hO' (R.obj L) k)
    (H : R.map (coherentMulIso O hO L n m).hom ≫
        (tensorPowerComparison O hO O' hO' R L β hunit (n + m)).hom ≫
        (tensorPowerReindex O' hO' (R.obj L) h).hom =
      (β (tensorPower O hO L n) (tensorPower O hO L m)).hom ≫
        (tensorSheafMapIso O' hO' (tensorPowerComparison O hO O' hO' R L β hunit n)
          (tensorPowerComparison O hO O' hO' R L β hunit m)).hom ≫ U.hom) :
    mulIsoOfComparison O hO O' hO' R L β hunit n m ≪≫
        tensorPowerReindex O' hO' (R.obj L) h = U :=
  Iso.ext <| (Category.assoc _ _ _).trans ((whisker_eq _ ((Category.assoc _ _ _).trans
    ((whisker_eq _ ((Category.assoc _ _ _).trans H)).trans
      (Iso.inv_hom_id_assoc _ _)))).trans (Iso.inv_hom_id_assoc _ _))

/-! ### The compatibilities of the tensorator taken as inputs -/

/-- Naturality of the tensorator in its first slot. -/
public def IsNaturalLeft : Prop :=
  ∀ {M M' N : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (u : M ⟶ M'),
    R.map (u ▷ N) ≫ (β M' N).hom = (β M N).hom ≫ (R.map u ▷ R.obj N)

/-- Naturality of the tensorator in its second slot. -/
public def IsNaturalRight : Prop :=
  ∀ {M N N' : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (v : N ⟶ N'),
    R.map (M ◁ v) ≫ (β M N').hom = (β M N).hom ≫ (R.obj M ◁ R.map v)

/-- Compatibility of the tensorator with the associativity constraints of the tensor product. -/
public def IsAssociative : Prop :=
  ∀ M N P : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO),
    R.map (α_ M N P).hom ≫ (β M (N ⊗ P)).hom ≫ (R.obj M ◁ (β N P).hom) =
      (β (M ⊗ N) P).hom ≫ ((β M N).hom ▷ R.obj P) ≫
        (α_ (R.obj M) (R.obj N) (R.obj P)).hom

/-- Compatibility of the tensorator with the left unit constraints of the tensor product. -/
public def IsLeftUnital : Prop :=
  ∀ M : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO),
    R.map (λ_ M).hom =
      (β (𝟙_ (_root_.SheafOfModules.{w}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))) M).hom ≫
        (hunit.hom ▷ R.obj M) ≫ (λ_ (R.obj M)).hom

/-- Compatibility of the tensorator with the symmetry constraints of the tensor product. -/
public def IsSymmetric : Prop :=
  ∀ M N : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO),
    R.map (β_ M N).hom ≫ (β N M).hom =
      (β M N).hom ≫ (β_ (R.obj M) (R.obj N)).hom

/-! ### The degree-`(n, 0)` normalisation -/

/-- Compatibility of the tensorator with the right unit constraints of the tensor product. -/
public def IsRightUnital : Prop :=
  ∀ M : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO),
    R.map (Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso O hO M).hom =
      (β M (_root_.SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))).hom ≫
        (tensorSheafMapIso O' hO' (Iso.refl (R.obj M)) hunit).hom ≫
        (Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso O' hO' (R.obj M)).hom

/-- The comparison of tensor powers carries the right unit constraint of the `n`-th power to the
right unit constraint of the `n`-th power of `R L`. -/
public theorem map_tensorSheafRightUnitor_tensorPowerComparison
    (hright : IsRightUnital O hO O' hO' R β hunit) (n : ℤ) :
    R.map (Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso O hO (tensorPower O hO L n)).hom ≫
        (tensorPowerComparison O hO O' hO' R L β hunit n).hom =
      (β (tensorPower O hO L n) (_root_.SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))).hom ≫
        (tensorSheafMapIso O' hO' (tensorPowerComparison O hO O' hO' R L β hunit n) hunit).hom ≫
        (Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso O' hO'
          (tensorPower O' hO' (R.obj L) n)).hom := by
  have e := whiskerLeft_rightUnitor_transfer
    (tensorPowerComparison O hO O' hO' R L β hunit n).hom hunit.hom
  rw [← MonoidalCategory.id_tensorHom, ← Iso.refl_hom, ← tensorSheafMapIso_hom_eq,
    ← tensorSheafMapIso_hom_eq, Stacks.SheafOfModules.rightUnitor_eq_tensorSheafRightUnitor,
    Stacks.SheafOfModules.rightUnitor_eq_tensorSheafRightUnitor] at e
  exact (eq_whisker (hright (tensorPower O hO L n)) _).trans
    ((Category.assoc _ _ _).trans (whisker_eq _ ((Category.assoc _ _ _).trans e)))

/-- The comparison of tensor powers carries the coherent multiplication in degree `(n, 0)` to the
right unit constraint of the tensor product sheaf. -/
public theorem mapTensorPowerIso_mul_zero_right
    (hright : IsRightUnital O hO O' hO' R β hunit) (n : ℤ) :
    R.map (coherentMulIso O hO L n 0).hom ≫
        (tensorPowerComparison O hO O' hO' R L β hunit (n + 0)).hom ≫
        (tensorPowerReindex O' hO' (R.obj L) (Int.add_zero n)).hom =
      (β (tensorPower O hO L n) (tensorPower O hO L 0)).hom ≫
        (tensorSheafMapIso O' hO' (tensorPowerComparison O hO O' hO' R L β hunit n)
          (tensorPowerComparison O hO O' hO' R L β hunit 0)).hom ≫
        (Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso O' hO'
          (tensorPower O' hO' (R.obj L) n)).hom := by
  simp only [tensorPower_zero, tensorPowerComparison_zero]
  exact (map_comp_reindex_of_eq_comp_inv O hO O' hO' R L β hunit (Int.add_zero n) _ _
    ((Iso.eq_comp_inv _).mpr
      (congrArg Iso.hom (coherentMulIso_zero_right_tensorSheaf O hO L n)))).trans
    (map_tensorSheafRightUnitor_tensorPowerComparison O hO O' hO' R L β hunit hright n)

/-- The transported multiplication satisfies the degree-`(n, 0)` normalisation: multiplying by
the zeroth power on the right is the right unit constraint of the tensor product sheaf. -/
public theorem mulIsoOfComparison_zero_right
    (hright : IsRightUnital O hO O' hO' R β hunit) (n : ℤ) :
    mulIsoOfComparison O hO O' hO' R L β hunit n 0 ≪≫
        tensorPowerReindex O' hO' (R.obj L) (Int.add_zero n) =
      Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso O' hO'
        (tensorPower O' hO' (R.obj L) n) :=
  mulIsoOfComparison_reindex_eq O hO O' hO' R L β hunit _ _
    (mapTensorPowerIso_mul_zero_right O hO O' hO' R L β hunit hright n)

/-! ### The degree-`(0, n)` normalisation -/

/-- The comparison of tensor powers carries the left unit constraint of the `n`-th power to the
left unit constraint of the `n`-th power of `R L`. -/
public theorem map_tensorSheafLeftUnitor_tensorPowerComparison
    (hleft : IsLeftUnital O hO O' hO' R β hunit) (n : ℤ) :
    R.map (Stacks.SheafOfModules.tensorSheafLeftUnitor O hO (tensorPower O hO L n)).hom ≫
        (tensorPowerComparison O hO O' hO' R L β hunit n).hom =
      (β (_root_.SheafOfModules.unit
            (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
          (tensorPower O hO L n)).hom ≫
        (tensorSheafMapIso O' hO' hunit (tensorPowerComparison O hO O' hO' R L β hunit n)).hom ≫
        (Stacks.SheafOfModules.tensorSheafLeftUnitor O' hO'
          (tensorPower O' hO' (R.obj L) n)).hom := by
  have e := whiskerRight_leftUnitor_transfer
    (tensorPowerComparison O hO O' hO' R L β hunit n).hom hunit.hom
  rw [← tensorSheafMapIso_hom_eq, Stacks.SheafOfModules.leftUnitor_eq_tensorSheafLeftUnitor O' hO'
    (tensorPower O' hO' (R.obj L) n)] at e
  have hl := hleft (tensorPower O hO L n)
  rw [Stacks.SheafOfModules.leftUnitor_eq_tensorSheafLeftUnitor O hO] at hl
  exact (eq_whisker hl _).trans
    ((Category.assoc _ _ _).trans (whisker_eq _ ((Category.assoc _ _ _).trans e)))

/-- The transported multiplication satisfies the degree-`(0, n)` normalisation: multiplying by
the zeroth power on the left is the left unit constraint of the tensor product sheaf. -/
public theorem mulIsoOfComparison_zero_left
    (hleft : IsLeftUnital O hO O' hO' R β hunit) (n : ℤ) :
    mulIsoOfComparison O hO O' hO' R L β hunit 0 n ≪≫
        tensorPowerReindex O' hO' (R.obj L) (Int.zero_add n) =
      Stacks.SheafOfModules.tensorSheafLeftUnitor O' hO' (tensorPower O' hO' (R.obj L) n) := by
  refine mulIsoOfComparison_reindex_eq O hO O' hO' R L β hunit _ _ ?_
  simp only [tensorPower_zero, tensorPowerComparison_zero]
  exact (map_comp_reindex_of_eq_comp_inv O hO O' hO' R L β hunit (Int.zero_add n) _ _
    ((Iso.eq_comp_inv _).mpr
      (congrArg Iso.hom (coherentMulIso_zero_left_tensorSheaf O hO L n)))).trans
    (map_tensorSheafLeftUnitor_tensorPowerComparison O hO O' hO' R L β hunit hleft n)

/-! ### The degree-`(n, 1)` normalisation -/

/-- The comparison of tensor powers carries the identification of the first power with `L` to
the identification of the first power with `R L`. -/
public theorem map_tensorPowerOneIso_tensorPowerComparison
    (hleft : IsLeftUnital O hO O' hO' R β hunit) :
    R.map (tensorPowerOneIso O hO L).hom =
      (tensorPowerComparison O hO O' hO' R L β hunit 1).hom ≫
        (tensorPowerOneIso O' hO' (R.obj L)).hom := by
  have key : R.map (Stacks.SheafOfModules.tensorSheafLeftUnitor O hO L).hom =
      (β (_root_.SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) L).hom ≫
        (hunit.hom ▷ R.obj L) ≫
        (Stacks.SheafOfModules.tensorSheafLeftUnitor O' hO' (R.obj L)).hom := by
    rw [← Stacks.SheafOfModules.leftUnitor_eq_tensorSheafLeftUnitor O hO L,
      ← Stacks.SheafOfModules.leftUnitor_eq_tensorSheafLeftUnitor O' hO' (R.obj L)]
    exact hleft L
  have hpc1 : (β (_root_.SheafOfModules.unit
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) L).hom ≫
        (hunit.hom ▷ R.obj L) =
      (tensorPowerComparison O hO O' hO' R L β hunit 1).hom := by
    rw [← tensorRightFunctor_map_iso_hom O' hO' hunit (R.obj L)]
    exact (congrArg Iso.hom (tensorPowerComparison_one O hO O' hO' R L β hunit)).symm
  refine key.trans ((Category.assoc _ _ _).symm.trans ?_)
  rw [hpc1, tensorPowerOneIso_eq_tensorSheafLeftUnitor O' hO' (R.obj L)]
  rfl

/-- The transported multiplication satisfies the degree-`(n, 1)` normalisation: multiplying by
the first power is one more iteration of right tensoring. -/
public theorem mulIsoOfComparison_one_right
    (hleft : IsLeftUnital O hO O' hO' R β hunit)
    (hnatR : IsNaturalRight O hO O' hO' R β) (n : ℤ) :
    mulIsoOfComparison O hO O' hO' R L β hunit n 1 =
      tensorSheafMapIso O' hO' (Iso.refl (tensorPower O' hO' (R.obj L) n))
          (tensorPowerOneIso O' hO' (R.obj L)) ≪≫
        tensorPowerSuccIso O' hO' (R.obj L) n := by
  refine iso_cancel_left (β (tensorPower O hO L n) (tensorPower O hO L 1) ≪≫
    tensorSheafMapIso O' hO' (tensorPowerComparison O hO O' hO' R L β hunit n)
      (tensorPowerComparison O hO O' hO' R L β hunit 1)) (Iso.ext ?_)
  have hone : (coherentMulIso O hO L n 1).hom =
      (tensorSheafMapIso O hO (Iso.refl (tensorPower O hO L n))
          (tensorPowerOneIso O hO L)).hom ≫ (tensorPowerSuccIso O hO L n).hom :=
    congrArg Iso.hom (coherentMulIso_one_right_tensorSheaf O hO L n)
  have h1 := map_tensorPowerOneIso_tensorPowerComparison O hO O' hO' R L β hunit hleft
  have hTl := congrArg Iso.hom
    (tensorSheafMapIso_refl_left O hO (tensorPower O hO L n) (tensorPowerOneIso O hO L))
  exact oneRight_transfer (mulIsoOfComparison_spec O hO O' hO' R L β hunit n 1)
    ((congrArg R.map (hone.trans (eq_whisker hTl _))).trans (R.map_comp _ _))
    (map_tensorPowerSuccIso_tensorPowerComparison O hO O' hO' R L β hunit n)
    (hnatR (tensorPowerOneIso O hO L).hom) h1 (tensorSheafMapIso_hom_eq O' hO' _ _)
    (congrArg Iso.hom (tensorSheafMapIso_refl_left O' hO' (tensorPower O' hO' (R.obj L) n)
      (tensorPowerOneIso O' hO' (R.obj L))))


/-! ### The associativity normalisation -/

/-- Naturality of the tensorator in its first slot, read from right to left. -/
@[reassoc]
public theorem beta_whiskerRight (hnatL : IsNaturalLeft O hO O' hO' R β)
    {A A' N : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (u : A ⟶ A') :
    (β A N).hom ≫ (R.map u ▷ R.obj N) = R.map (u ▷ N) ≫ (β A' N).hom := (hnatL u).symm

/-- Naturality of the tensorator in its second slot, read from right to left. -/
@[reassoc]
public theorem beta_whiskerLeft (hnatR : IsNaturalRight O hO O' hO' R β)
    {A N N' : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (v : N ⟶ N') :
    (β A N).hom ≫ (R.obj A ◁ R.map v) = R.map (A ◁ v) ≫ (β A N').hom := (hnatR v).symm

/-- Compatibility of the tensorator with the associator, read from right to left. -/
@[reassoc]
public theorem beta_associator (hassoc : IsAssociative O hO O' hO' R β)
    (A N P : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    (β (A ⊗ N) P).hom ≫ ((β A N).hom ▷ R.obj P) ≫
        (α_ (R.obj A) (R.obj N) (R.obj P)).hom =
      R.map (α_ A N P).hom ≫ (β A (N ⊗ P)).hom ≫ (R.obj A ◁ (β N P).hom) :=
  (hassoc A N P).symm

/-- The associativity normalisation of the coherent multiplication, stated against
the associativity constraint of the tensor product sheaf. -/
public theorem coherentMulIso_assoc_tensorSheaf (n m k : ℤ) :
    tensorSheafMapIso O hO (coherentMulIso O hO L n m)
          (Iso.refl (tensorPower O hO L k)) ≪≫
        coherentMulIso O hO L (n + m) k =
      Stacks.SheafOfModules.tensorSheafAssociator O hO (tensorPower O hO L n)
          (tensorPower O hO L m) (tensorPower O hO L k) ≪≫
        tensorSheafMapIso O hO (Iso.refl (tensorPower O hO L n))
          (coherentMulIso O hO L m k) ≪≫
        coherentMulIso O hO L n (m + k) ≪≫
        tensorPowerReindex O hO L (Int.add_assoc n m k).symm :=
  (tensorPowerCoherence O hO L).mul_assoc n m k

/-- The left-hand side of the associativity law for the transported multiplication, preceded by
the tensorator and the comparisons, is the image under `R` of the left-hand side of the
associativity law for `L`, followed by the comparison. -/
public theorem mulIsoOfComparison_assoc_left
    (hnatL : IsNaturalLeft O hO O' hO' R β) (n m k : ℤ) :
    (β (tensorPower O hO L n ⊗ tensorPower O hO L m) (tensorPower O hO L k)).hom ≫
        (((β (tensorPower O hO L n) (tensorPower O hO L m)).hom ≫
            ((tensorPowerComparison O hO O' hO' R L β hunit n).hom ⊗ₘ
              (tensorPowerComparison O hO O' hO' R L β hunit m).hom)) ⊗ₘ
          (tensorPowerComparison O hO O' hO' R L β hunit k).hom) ≫
        (@MonoidalCategory.whiskerRight _ _
          (Stacks.SheafOfModules.Strict.monoidalCategory O' hO').toMonoidalCategoryStruct _ _
          (mulIsoOfComparison O hO O' hO' R L β hunit n m).hom
          (tensorPower O' hO' (R.obj L) k)) ≫
        (mulIsoOfComparison O hO O' hO' R L β hunit (n + m) k).hom =
      R.map (@MonoidalCategory.whiskerRight _ _
        (Stacks.SheafOfModules.Strict.monoidalCategory O hO).toMonoidalCategoryStruct _ _
        (coherentMulIso O hO L n m).hom (tensorPower O hO L k)) ≫
        R.map (coherentMulIso O hO L (n + m) k).hom ≫
        (tensorPowerComparison O hO O' hO' R L β hunit (n + m + k)).hom :=
  assocLeft_transfer
    ((Category.assoc _ _ _).trans (mulIsoOfComparison_spec_tensorHom O hO O' hO' R L β hunit n m))
    (beta_whiskerRight O hO O' hO' R β hnatL (coherentMulIso O hO L n m).hom)
    (mulIsoOfComparison_spec_tensorHom O hO O' hO' R L β hunit (n + m) k)

/-- The right-hand side of the associativity law for the transported multiplication, preceded by
the tensorator and the comparisons, is the image under `R` of the right-hand side of the
associativity law for `L`, followed by the comparison. -/
public theorem mulIsoOfComparison_assoc_right
    (hnatR : IsNaturalRight O hO O' hO' R β) (hassoc : IsAssociative O hO O' hO' R β)
    (n m k : ℤ) :
    (β (tensorPower O hO L n ⊗ tensorPower O hO L m) (tensorPower O hO L k)).hom ≫
        (((β (tensorPower O hO L n) (tensorPower O hO L m)).hom ≫
            ((tensorPowerComparison O hO O' hO' R L β hunit n).hom ⊗ₘ
              (tensorPowerComparison O hO O' hO' R L β hunit m).hom)) ⊗ₘ
          (tensorPowerComparison O hO O' hO' R L β hunit k).hom) ≫
        (α_ (tensorPower O' hO' (R.obj L) n) (tensorPower O' hO' (R.obj L) m)
          (tensorPower O' hO' (R.obj L) k)).hom ≫
        (tensorPower O' hO' (R.obj L) n ◁
          (mulIsoOfComparison O hO O' hO' R L β hunit m k).hom) ≫
        (mulIsoOfComparison O hO O' hO' R L β hunit n (m + k)).hom ≫
        (tensorPowerReindex O' hO' (R.obj L) (Int.add_assoc n m k).symm).hom =
      R.map (α_ (tensorPower O hO L n) (tensorPower O hO L m)
          (tensorPower O hO L k)).hom ≫
        R.map (tensorPower O hO L n ◁ (coherentMulIso O hO L m k).hom) ≫
        R.map (coherentMulIso O hO L n (m + k)).hom ≫
        R.map (tensorPowerReindex O hO L (Int.add_assoc n m k).symm).hom ≫
        (tensorPowerComparison O hO O' hO' R L β hunit (n + m + k)).hom :=
  assocRight_transfer (beta_associator O hO O' hO' R β hassoc _ _ _)
    (mulIsoOfComparison_spec_tensorHom O hO O' hO' R L β hunit m k)
    (beta_whiskerLeft O hO O' hO' R β hnatR (coherentMulIso O hO L m k).hom)
    (mulIsoOfComparison_spec_tensorHom O hO O' hO' R L β hunit n (m + k))
    (tensorPowerComparison_reindex O hO O' hO' R L β hunit (Int.add_assoc n m k).symm)

/-- The transported multiplication satisfies the associativity normalisation: it respects the
associativity constraint of the tensor product sheaf. -/
public theorem mulIsoOfComparison_assoc
    (hnatL : IsNaturalLeft O hO O' hO' R β) (hnatR : IsNaturalRight O hO O' hO' R β)
    (hassoc : IsAssociative O hO O' hO' R β) (n m k : ℤ) :
    tensorSheafMapIso O' hO' (mulIsoOfComparison O hO O' hO' R L β hunit n m)
          (Iso.refl (tensorPower O' hO' (R.obj L) k)) ≪≫
        mulIsoOfComparison O hO O' hO' R L β hunit (n + m) k =
      Stacks.SheafOfModules.tensorSheafAssociator O' hO' (tensorPower O' hO' (R.obj L) n)
          (tensorPower O' hO' (R.obj L) m) (tensorPower O' hO' (R.obj L) k) ≪≫
        tensorSheafMapIso O' hO' (Iso.refl (tensorPower O' hO' (R.obj L) n))
          (mulIsoOfComparison O hO O' hO' R L β hunit m k) ≪≫
        mulIsoOfComparison O hO O' hO' R L β hunit n (m + k) ≪≫
        tensorPowerReindex O' hO' (R.obj L) (Int.add_assoc n m k).symm := by
  have hsrcR : R.map (@MonoidalCategory.whiskerRight _ _
        (Stacks.SheafOfModules.Strict.monoidalCategory O hO).toMonoidalCategoryStruct _ _
        (coherentMulIso O hO L n m).hom (tensorPower O hO L k)) ≫
        R.map (coherentMulIso O hO L (n + m) k).hom ≫
        (tensorPowerComparison O hO O' hO' R L β hunit (n + m + k)).hom =
      R.map (α_ (tensorPower O hO L n) (tensorPower O hO L m)
          (tensorPower O hO L k)).hom ≫
        R.map (tensorPower O hO L n ◁ (coherentMulIso O hO L m k).hom) ≫
        R.map (coherentMulIso O hO L n (m + k)).hom ≫
        R.map (tensorPowerReindex O hO L (Int.add_assoc n m k).symm).hom ≫
        (tensorPowerComparison O hO O' hO' R L β hunit (n + m + k)).hom := by
    have hsrc : (@MonoidalCategory.whiskerRight _ _
          (Stacks.SheafOfModules.Strict.monoidalCategory O hO).toMonoidalCategoryStruct _ _
          (coherentMulIso O hO L n m).hom (tensorPower O hO L k)) ≫
          (coherentMulIso O hO L (n + m) k).hom =
        (α_ (tensorPower O hO L n) (tensorPower O hO L m)
            (tensorPower O hO L k)).hom ≫
          (tensorPower O hO L n ◁ (coherentMulIso O hO L m k).hom) ≫
          (coherentMulIso O hO L n (m + k)).hom ≫
          (tensorPowerReindex O hO L (Int.add_assoc n m k).symm).hom := by
      have h := congrArg Iso.hom (coherentMulIso_assoc_tensorSheaf O hO L n m k)
      have e₁ := (tensorSheafMapIso_hom_eq O hO (coherentMulIso O hO L n m)
        (Iso.refl (tensorPower O hO L k))).trans (MonoidalCategory.tensorHom_id _ _)
      have eα := (congrArg Iso.hom (Stacks.SheafOfModules.associator_eq_tensorSheafAssociator O hO
        (tensorPower O hO L n) (tensorPower O hO L m) (tensorPower O hO L k))).symm
      have e₂ := (tensorSheafMapIso_hom_eq O hO (Iso.refl (tensorPower O hO L n))
        (coherentMulIso O hO L m k)).trans (MonoidalCategory.id_tensorHom _ _)
      exact ((eq_whisker e₁ _).symm.trans h).trans
        ((eq_whisker eα _).trans (whisker_eq _ (eq_whisker e₂ _)))
    exact map_comp_transfer R hsrc _
  refine iso_cancel_left
    (β (tensorPower O hO L n ⊗ tensorPower O hO L m) (tensorPower O hO L k) ≪≫
      tensorSheafMapIso O' hO' (β (tensorPower O hO L n) (tensorPower O hO L m) ≪≫
          tensorSheafMapIso O' hO' (tensorPowerComparison O hO O' hO' R L β hunit n)
            (tensorPowerComparison O hO O' hO' R L β hunit m))
        (tensorPowerComparison O hO O' hO' R L β hunit k)) (Iso.ext ?_)
  exact assoc_transfer (tensorSheafMapIso_hom_eq O' hO' _ _)
    (tensorSheafMapIso_hom_eq O' hO' _ _)
    ((tensorSheafMapIso_hom_eq O' hO' _ _).trans (MonoidalCategory.tensorHom_id _ _))
    (congrArg Iso.hom (Stacks.SheafOfModules.associator_eq_tensorSheafAssociator O' hO' _ _ _)).symm
    ((tensorSheafMapIso_hom_eq O' hO' _ _).trans (MonoidalCategory.id_tensorHom _ _))
    (mulIsoOfComparison_assoc_left O hO O' hO' R L β hunit hnatL n m k)
    (mulIsoOfComparison_assoc_right O hO O' hO' R L β hunit hnatR hassoc n m k) hsrcR

/-! ### The commutativity normalisation -/

/-- The commutativity normalisation of the coherent multiplication, stated against
the symmetry constraint of the tensor product sheaf. -/
public theorem coherentMulIso_comm_tensorSheaf (n m : ℤ) :
    coherentMulIso O hO L n m =
      Stacks.SheafOfModules.tensorSheafBraiding O hO (tensorPower O hO L n)
          (tensorPower O hO L m) ≪≫
        coherentMulIso O hO L m n ≪≫ tensorPowerReindex O hO L (Int.add_comm m n) :=
  (tensorPowerCoherence O hO L).mul_comm n m

/-- The transported multiplication satisfies the commutativity normalisation: it is unchanged by
the symmetry constraint of the tensor product sheaf. -/
public theorem mulIsoOfComparison_comm
    (hsym : IsSymmetric O hO O' hO' R β) (n m : ℤ) :
    mulIsoOfComparison O hO O' hO' R L β hunit n m =
      Stacks.SheafOfModules.tensorSheafBraiding O' hO' (tensorPower O' hO' (R.obj L) n)
          (tensorPower O' hO' (R.obj L) m) ≪≫
        mulIsoOfComparison O hO O' hO' R L β hunit m n ≪≫
        tensorPowerReindex O' hO' (R.obj L) (Int.add_comm m n) := by
  refine iso_cancel_left (β (tensorPower O hO L n) (tensorPower O hO L m) ≪≫
    tensorSheafMapIso O' hO' (tensorPowerComparison O hO O' hO' R L β hunit n)
      (tensorPowerComparison O hO O' hO' R L β hunit m)) (Iso.ext ?_)
  have hre := tensorPowerComparison_reindex O hO O' hO' R L β hunit (Int.add_comm m n)
  have hcomm : (coherentMulIso O hO L n m).hom =
      (β_ (tensorPower O hO L n) (tensorPower O hO L m)).hom ≫
        (coherentMulIso O hO L m n).hom ≫
        (tensorPowerReindex O hO L (Int.add_comm m n)).hom := by
    rw [Stacks.SheafOfModules.braiding_eq_tensorSheafBraiding]
    exact congrArg Iso.hom (coherentMulIso_comm_tensorSheaf O hO L n m)
  exact comm_transfer (mulIsoOfComparison_spec O hO O' hO' R L β hunit n m)
    ((congrArg R.map hcomm).trans ((R.map_comp _ _).trans (whisker_eq _ (R.map_comp _ _))))
    hre (tensorSheafMapIso_hom_eq O' hO' _ _)
    (congrArg Iso.hom (Stacks.SheafOfModules.braiding_eq_tensorSheafBraiding O' hO' _ _)).symm
    (hsym _ _) (tensorSheafMapIso_hom_eq O' hO' _ _)
    (mulIsoOfComparison_spec O hO O' hO' R L β hunit m n)

/-! ### The transported multiplication is the coherent multiplication -/

/-- The transported multiplication, as a coherent multiplication on the integral tensor powers
of `R L`: it satisfies the two unit normalisations, the degree-`(n, 1)` normalisation,
associativity and commutativity. -/
public def tensorPowerCoherenceOfComparison
    (hleft : IsLeftUnital O hO O' hO' R β hunit)
    (hright : IsRightUnital O hO O' hO' R β hunit)
    (hnatL : IsNaturalLeft O hO O' hO' R β) (hnatR : IsNaturalRight O hO O' hO' R β)
    (hassoc : IsAssociative O hO O' hO' R β) (hsym : IsSymmetric O hO O' hO' R β) :
    TensorPowerCoherence O' hO' (R.obj L) where
  isInvertible := isInvertible_tensorPower O' hO' (R.obj L)
  mulIso := mulIsoOfComparison O hO O' hO' R L β hunit
  mul_zero_left := mulIsoOfComparison_zero_left O hO O' hO' R L β hunit hleft
  mul_zero_right := mulIsoOfComparison_zero_right O hO O' hO' R L β hunit hright
  mul_one_right := mulIsoOfComparison_one_right O hO O' hO' R L β hunit hleft hnatR
  pow_succ_natural n _ _ f := tensorPowerSuccIso_natural O' hO' (R.obj L) n f
  mul_assoc := mulIsoOfComparison_assoc O hO O' hO' R L β hunit hnatL hnatR hassoc
  mul_comm := mulIsoOfComparison_comm O hO O' hO' R L β hunit hsym

/-- The transported multiplication is the coherent multiplication for `R L`. -/
public theorem mulIsoOfComparison_eq
    (hleft : IsLeftUnital O hO O' hO' R β hunit)
    (hright : IsRightUnital O hO O' hO' R β hunit)
    (hnatL : IsNaturalLeft O hO O' hO' R β) (hnatR : IsNaturalRight O hO O' hO' R β)
    (hassoc : IsAssociative O hO O' hO' R β) (hsym : IsSymmetric O hO O' hO' R β) (n m : ℤ) :
    mulIsoOfComparison O hO O' hO' R L β hunit n m = coherentMulIso O' hO' (R.obj L) n m :=
  coherentMulIso_eq O' hO' (R.obj L)
    (tensorPowerCoherenceOfComparison O hO O' hO' R L β hunit hleft hright hnatL hnatR hassoc
      hsym) n m

/-- The comparison of integral tensor powers is multiplicative: it carries the coherent
multiplication `L^{⊗ n} ⊗ L^{⊗ m} ≅ L^{⊗ (n + m)}` for `L` to the one for `R L`, in every pair of
degrees. -/
@[reassoc]
public theorem map_coherentMulIso_tensorPowerComparison
    (hleft : IsLeftUnital O hO O' hO' R β hunit)
    (hright : IsRightUnital O hO O' hO' R β hunit)
    (hnatL : IsNaturalLeft O hO O' hO' R β) (hnatR : IsNaturalRight O hO O' hO' R β)
    (hassoc : IsAssociative O hO O' hO' R β) (hsym : IsSymmetric O hO O' hO' R β) (n m : ℤ) :
    R.map (coherentMulIso O hO L n m).hom ≫
        (tensorPowerComparison O hO O' hO' R L β hunit (n + m)).hom =
      (β (tensorPower O hO L n) (tensorPower O hO L m)).hom ≫
        (tensorSheafMapIso O' hO' (tensorPowerComparison O hO O' hO' R L β hunit n)
          (tensorPowerComparison O hO O' hO' R L β hunit m)).hom ≫
        (coherentMulIso O' hO' (R.obj L) n m).hom := by
  rw [← mulIsoOfComparison_eq O hO O' hO' R L β hunit hleft hright hnatL hnatR hassoc hsym,
    mulIsoOfComparison_spec]

end Stacks.SheafOfModules.TensorPower

end
