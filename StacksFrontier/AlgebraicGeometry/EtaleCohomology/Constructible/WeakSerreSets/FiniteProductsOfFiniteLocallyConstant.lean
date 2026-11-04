module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreSets.FiniteLocallyConstantClosure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerreSets.FiniteLimitsFromProductsAndEqualizers

/-!
# Finite locally constant sheaves of sets are closed under finite products

Let `J` be a Grothendieck topology on `C`. Finite local constancy of a sheaf of sets is stable
under finite products inside `Sheaf J (Type w)`, for an arbitrary carrier universe `w` and with
no hypothesis beyond weak sheafification on the localized sites.

Two inputs make this work without any exactness property of sheafification. The first is that the
constant sheaf functor preserves binary products: the comparison
`Stacks.ConstantSheaf.constantSheafProdComparison` from the constant sheaf on `A × B` to the
product of the constant sheaves is locally bijective, hence an isomorphism. Local surjectivity is
the local surjectivity of the sheafification unit on each factor, and local injectivity is the
dichotomy of `Stacks.ConstantSheaf.constant_unit_map_eq_of_pair_eq`: two distinct constants which
agree at an object force *all* constants of *every* set to agree there. The second is that
restriction to a localized site preserves products
(`CategoryTheory.GrothendieckTopology.preservesLimitsOfShape_overPullback`).

Combined with the terminal case of
`Stacks.ConstantSheaf.isClosedUnderLimitsOfShape_pempty_isFiniteLocallyConstant` this gives
closure under all finite products. What is *not* proved here is closure under equalizers, which
is the remaining half of the finite-limit assertion of Tag 093U for sheaves of sets.

## Main results

* `Stacks.ConstantSheaf.isIso_constantSheafProdComparison` — the constant sheaf functor on sets
  preserves binary products.
* `Stacks.ConstantSheaf.isFiniteLocallyConstant_prod` — a binary product of finite locally
  constant sheaves of sets is finite locally constant.
* `Stacks.ConstantSheaf.isClosedUnderFiniteProducts_isFiniteLocallyConstant` — closure under all
  finite products.

## References

* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafProduct

universe w v u

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)

variable {X Y : Sheaf K (Type w)}

/-- The sections over `U` of a binary product of sheaves of sets are the pairs of sections of the
two factors over `U`. -/
def prodSectionsIso (U : Cᵒᵖ) : (X ⨯ Y).obj.obj U ≅ X.obj.obj U × Y.obj.obj U :=
  IsLimit.conePointUniqueUpToIso
    (isLimitMapConeBinaryFanEquiv
      (sheafToPresheaf K (Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj U) _ _
      (isLimitOfPreserves
        (sheafToPresheaf K (Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj U) (prodIsProd X Y)))
    (Types.binaryProductLimit (X.obj.obj U) (Y.obj.obj U))

/-- Each coordinate of `prodSectionsIso` is the corresponding projection of the product. -/
private lemma prodSectionsIso_hom_comp (U : Cᵒᵖ) (j : Discrete WalkingPair)
    (s : (X ⨯ Y).obj.obj U) :
    (Types.binaryProductCone (X.obj.obj U) (Y.obj.obj U)).π.app j
        ((prodSectionsIso K U).hom s) =
      (BinaryFan.mk ((prod.fst : X ⨯ Y ⟶ X).hom.app U) ((prod.snd : X ⨯ Y ⟶ Y).hom.app U)).π.app
        j s :=
  congrArg (fun f => f s) (IsLimit.conePointUniqueUpToIso_hom_comp
    (isLimitMapConeBinaryFanEquiv
      (sheafToPresheaf K (Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj U)
      (prod.fst : X ⨯ Y ⟶ X) prod.snd
      (isLimitOfPreserves
        (sheafToPresheaf K (Type w) ⋙ (evaluation Cᵒᵖ (Type w)).obj U) (prodIsProd X Y)))
    (Types.binaryProductLimit (X.obj.obj U) (Y.obj.obj U)) j)

/-- The first coordinate of `prodSectionsIso` is the first projection of the product. -/
lemma prodSectionsIso_fst (U : Cᵒᵖ) (s : (X ⨯ Y).obj.obj U) :
    ((prodSectionsIso K U).hom s).1 = (prod.fst : X ⨯ Y ⟶ X).hom.app U s :=
  prodSectionsIso_hom_comp K U ⟨WalkingPair.left⟩ s

/-- The second coordinate of `prodSectionsIso` is the second projection of the product. -/
lemma prodSectionsIso_snd (U : Cᵒᵖ) (s : (X ⨯ Y).obj.obj U) :
    ((prodSectionsIso K U).hom s).2 = (prod.snd : X ⨯ Y ⟶ Y).hom.app U s :=
  prodSectionsIso_hom_comp K U ⟨WalkingPair.right⟩ s

/-- Two sections of a binary product of sheaves of sets agree as soon as their two projections
do. -/
lemma prod_section_ext (U : Cᵒᵖ) {s t : (X ⨯ Y).obj.obj U}
    (h₁ : (prod.fst : X ⨯ Y ⟶ X).hom.app U s = (prod.fst : X ⨯ Y ⟶ X).hom.app U t)
    (h₂ : (prod.snd : X ⨯ Y ⟶ Y).hom.app U s = (prod.snd : X ⨯ Y ⟶ Y).hom.app U t) :
    s = t := by
  refine (ConcreteCategory.bijective_of_isIso (prodSectionsIso K U).hom).injective
    (Prod.ext ?_ ?_)
  · rwa [prodSectionsIso_fst, prodSectionsIso_fst]
  · rwa [prodSectionsIso_snd, prodSectionsIso_snd]

end Stacks.SheafProduct

namespace Stacks.ConstantSheaf

universe w v u

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C)

section Comparison

variable [HasWeakSheafify K (Type w)]

/-- A map of sets, applied to a constant section, is the constant section of the image. -/
lemma constantSheaf_map_app_toSheafify
    (A B : Type w) (f : A ⟶ B) (U : Cᵒᵖ) (a : A) :
    ((constantSheaf K (Type w)).map f).hom.app U
        ((CategoryTheory.toSheafify K ((Functor.const Cᵒᵖ).obj A)).app U a) =
      (CategoryTheory.toSheafify K ((Functor.const Cᵒᵖ).obj B)).app U (f a) :=
  (congrArg (fun t => t.app U a)
    (CategoryTheory.toSheafify_naturality K ((Functor.const Cᵒᵖ).map f))).symm

/-- The comparison map from the constant sheaf on a product of two sets to the product of the two
constant sheaves. -/
def constantSheafProdComparison (A B : Type w) :
    (constantSheaf K (Type w)).obj (A × B) ⟶
      (constantSheaf K (Type w)).obj A ⨯ (constantSheaf K (Type w)).obj B :=
  prod.lift ((constantSheaf K (Type w)).map (TypeCat.ofHom Prod.fst))
    ((constantSheaf K (Type w)).map (TypeCat.ofHom Prod.snd))

/-- On sections, the first projection after `constantSheafProdComparison` is the image under the
constant sheaf functor of the first projection `A × B → A`. -/
lemma constantSheafProdComparison_fst_app (A B : Type w) (U : Cᵒᵖ)
    (x : ((constantSheaf K (Type w)).obj (A × B)).obj.obj U) :
    (prod.fst : _ ⟶ (constantSheaf K (Type w)).obj A).hom.app U
        ((constantSheafProdComparison K A B).hom.app U x) =
      ((constantSheaf K (Type w)).map (TypeCat.ofHom Prod.fst)).hom.app U x :=
  congrArg (fun (z : (constantSheaf K (Type w)).obj (A × B) ⟶ _) => z.hom.app U x)
    (prod.lift_fst _ _)

/-- On sections, the second projection after `constantSheafProdComparison` is the image under the
constant sheaf functor of the second projection `A × B → B`. -/
lemma constantSheafProdComparison_snd_app (A B : Type w) (U : Cᵒᵖ)
    (x : ((constantSheaf K (Type w)).obj (A × B)).obj.obj U) :
    (prod.snd : _ ⟶ (constantSheaf K (Type w)).obj B).hom.app U
        ((constantSheafProdComparison K A B).hom.app U x) =
      ((constantSheaf K (Type w)).map (TypeCat.ofHom Prod.snd)).hom.app U x :=
  congrArg (fun (z : (constantSheaf K (Type w)).obj (A × B) ⟶ _) => z.hom.app U x)
    (prod.lift_snd _ _)

/-- The first component of the product comparison, on a constant section, is the constant section
of the first coordinate. -/
lemma constantSheafProdComparison_fst_toSheafify (A B : Type w) (U : Cᵒᵖ) (p : A × B) :
    (prod.fst : _ ⟶ (constantSheaf K (Type w)).obj A).hom.app U
        ((constantSheafProdComparison K A B).hom.app U
          ((CategoryTheory.toSheafify K ((Functor.const Cᵒᵖ).obj (A × B))).app U p)) =
      (CategoryTheory.toSheafify K ((Functor.const Cᵒᵖ).obj A)).app U p.1 :=
  (constantSheafProdComparison_fst_app K A B U _).trans
    (constantSheaf_map_app_toSheafify K (A × B) A (TypeCat.ofHom Prod.fst) U p)

/-- The second component of the product comparison, on a constant section, is the constant
section of the second coordinate. -/
lemma constantSheafProdComparison_snd_toSheafify (A B : Type w) (U : Cᵒᵖ) (p : A × B) :
    (prod.snd : _ ⟶ (constantSheaf K (Type w)).obj B).hom.app U
        ((constantSheafProdComparison K A B).hom.app U
          ((CategoryTheory.toSheafify K ((Functor.const Cᵒᵖ).obj (A × B))).app U p)) =
      (CategoryTheory.toSheafify K ((Functor.const Cᵒᵖ).obj B)).app U p.2 :=
  (constantSheafProdComparison_snd_app K A B U _).trans
    (constantSheaf_map_app_toSheafify K (A × B) B (TypeCat.ofHom Prod.snd) U p)

/-- The product comparison for constant sheaves of sets is injective on sections. -/
lemma injective_constantSheafProdComparison (A B : Type w) (U : Cᵒᵖ) :
    Function.Injective ((constantSheafProdComparison K A B).hom.app U) := by
  refine injective_of_const_eq_imp K (A × B) _ _
    (CategoryTheory.toSheafify K ((Functor.const Cᵒᵖ).obj (A × B)))
    (constantSheafProdComparison K A B) ?_ U
  intro V p q hpq
  have h₁ := (constantSheafProdComparison_fst_toSheafify K A B (op V) p).symm.trans
    ((congrArg
      (fun z => (prod.fst : _ ⟶ (constantSheaf K (Type w)).obj A).hom.app (op V) z) hpq).trans
      (constantSheafProdComparison_fst_toSheafify K A B (op V) q))
  have h₂ := (constantSheafProdComparison_snd_toSheafify K A B (op V) p).symm.trans
    ((congrArg
      (fun z => (prod.snd : _ ⟶ (constantSheaf K (Type w)).obj B).hom.app (op V) z) hpq).trans
      (constantSheafProdComparison_snd_toSheafify K A B (op V) q))
  by_cases hA : p.1 = q.1
  · by_cases hB : p.2 = q.2
    · rw [Prod.ext hA hB]
    · exact constant_unit_map_eq_of_pair_eq K B (A × B) V hB h₂ p q
  · exact constant_unit_map_eq_of_pair_eq K A (A × B) V hA h₁ p q

/-- The product comparison for constant sheaves of sets is locally surjective. -/
lemma locallySurjective_constantSheafProdComparison (A B : Type w) :
    Presheaf.IsLocallySurjective K (constantSheafProdComparison K A B).hom := by
  have key : Presheaf.IsLocallySurjective K
      (CategoryTheory.toSheafify K ((Functor.const Cᵒᵖ).obj (A × B)) ≫
        (constantSheafProdComparison K A B).hom) := by
    constructor
    intro R s
    have hA := Presheaf.imageSieve_mem (J := K)
      (f := CategoryTheory.toSheafify K ((Functor.const Cᵒᵖ).obj A))
      (s := (prod.fst : _ ⟶ (constantSheaf K (Type w)).obj A).hom.app (op R) s)
    have hB := Presheaf.imageSieve_mem (J := K)
      (f := CategoryTheory.toSheafify K ((Functor.const Cᵒᵖ).obj B))
      (s := (prod.snd : _ ⟶ (constantSheaf K (Type w)).obj B).hom.app (op R) s)
    refine K.superset_covering ?_ (K.intersection_covering hA hB)
    rintro V i ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨(a, b), Stacks.SheafProduct.prod_section_ext K (op V) ?_ ?_⟩
    · exact (constantSheafProdComparison_fst_toSheafify K A B (op V) (a, b)).trans
        (ha.trans (NatTrans.naturality_apply
          (prod.fst : _ ⟶ (constantSheaf K (Type w)).obj A).hom i.op s).symm)
    · exact (constantSheafProdComparison_snd_toSheafify K A B (op V) (a, b)).trans
        (hb.trans (NatTrans.naturality_apply
          (prod.snd : _ ⟶ (constantSheaf K (Type w)).obj B).hom i.op s).symm)
  exact Presheaf.isLocallySurjective_of_isLocallySurjective K
    (CategoryTheory.toSheafify K ((Functor.const Cᵒᵖ).obj (A × B)))
    (constantSheafProdComparison K A B).hom

/-- **The constant sheaf functor on sets preserves binary products.** -/
instance isIso_constantSheafProdComparison (A B : Type w) :
    IsIso (constantSheafProdComparison K A B) :=
  (Sheaf.isLocallyBijective_iff_isIso _).mp
    ⟨Presheaf.isLocallyInjective_of_injective K _
      (injective_constantSheafProdComparison K A B),
      locallySurjective_constantSheafProdComparison K A B⟩

/-- The constant sheaf on `A × B` is a product of the constant sheaves on `A` and on `B`. -/
def constantSheafProdIso (A B : Type w) :
    (constantSheaf K (Type w)).obj (A × B) ≅
      (constantSheaf K (Type w)).obj A ⨯ (constantSheaf K (Type w)).obj B :=
  asIso (constantSheafProdComparison K A B)

end Comparison

section Closure

variable [∀ U : C, HasWeakSheafify (K.over U) (Type w)]

/-- **A binary product of finite locally constant sheaves of sets is finite locally constant.** -/
lemma isFiniteLocallyConstant_prod (F G : Sheaf K (Type w))
    [IsFiniteLocallyConstant K F] [IsFiniteLocallyConstant K G] :
    IsFiniteLocallyConstant K (F ⨯ G) where
  exists_finite_cover U := by
    obtain ⟨I, X, f, hf, h⟩ := exists_cover_isConstantWith_pair K Finite F G
      (fun V => IsFiniteLocallyConstant.exists_finite_cover (J := K) (FD := TypeCat.Fun)
        (CD := fun A : Type w => A) (F := F) V)
      (fun V => IsFiniteLocallyConstant.exists_finite_cover (J := K) (FD := TypeCat.Fun)
        (CD := fun A : Type w => A) (F := G) V) U
    refine ⟨I, X, f, hf, fun i => ?_⟩
    obtain ⟨⟨A, (_ : Finite A), ⟨eF⟩⟩, ⟨B, (_ : Finite B), ⟨eG⟩⟩⟩ := h i
    exact ⟨A × B, inferInstance,
      ⟨constantSheafProdIso (K.over (X i)) A B ≪≫ prod.mapIso eF eG ≪≫
        (PreservesLimitPair.iso (K.overPullback (Type w) (X i)) F G).symm⟩⟩

/-- Finite locally constant sheaves of sets are closed under binary products. -/
instance isClosedUnderBinaryProducts_isFiniteLocallyConstant :
    ObjectProperty.IsClosedUnderBinaryProducts
      (fun F : Sheaf K (Type w) => IsFiniteLocallyConstant K F) := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro Z ⟨D, hD⟩
  refine ObjectProperty.prop_of_iso _
    (HasLimit.isoOfNatIso (diagramIsoPair D)).symm ?_
  have h₁ : IsFiniteLocallyConstant K (D.obj ⟨WalkingPair.left⟩) := hD _
  have h₂ : IsFiniteLocallyConstant K (D.obj ⟨WalkingPair.right⟩) := hD _
  exact isFiniteLocallyConstant_prod K _ _

/-- **Finite locally constant sheaves of sets are closed under finite products.** -/
instance isClosedUnderFiniteProducts_isFiniteLocallyConstant :
    ObjectProperty.IsClosedUnderFiniteProducts
      (fun F : Sheaf K (Type w) => IsFiniteLocallyConstant K F) :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

end Closure

end Stacks.ConstantSheaf

end
