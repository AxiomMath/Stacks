module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Topology.Sheaves.Over
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Bound07QAHypotheses

/-!
# The annihilation of [Stacks, Tag 07Q9] is a local condition on `X`

For a morphism `α` of `D⁺(Ab(X_Zar))`, the annihilation `Annihilation07Q9` — `q • 𝟙` vanishes on
every cohomology sheaf of a cone of `α` — holds as soon as it holds for the restrictions of `α`
to the members of an open covering of `X`. Restriction of abelian sheaves to an open `U` is taken
along the localized site `(X_Zar)/U`, whose objects are the opens of `X` contained in `U`; it is
exact.

## Main definitions

* `Stacks.Triangulated.ConeHomologyAnnihilation`: for a morphism `α` of `D⁺(𝒜)`, `q` annihilates
  the cohomology objects of every cone of `α`.
* `Stacks.ExactDerivedPlus.mapDerivedCategoryPlusHomologyIso`: an exact functor commutes with the
  cohomology objects of bounded below derived categories.
* `Crystalline.GlobalCrystallineSituation.SmallSite.opensOverRestriction`: restriction of abelian
  sheaves on `X_Zar` to the localized site at an open `U`.

## Main results

* `Stacks.ExactDerivedPlus.isTriangulated_mapDerivedCategoryPlus`: an exact functor acts
  triangulatedly on bounded below derived categories.
* `Stacks.Triangulated.coneHomologyAnnihilation_iff_of_distTriang`: one cone suffices.
* `Stacks.Triangulated.coneHomologyAnnihilation_map`: `ConeHomologyAnnihilation` transports along
  a triangulated functor whose cohomology objects are computed by an additive functor.
* In the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`:
  * `smul_id_eq_zero_of_forall_le`: `q • 𝟙 M = 0` is local on `X` for an abelian sheaf `M`.
  * `annihilation07Q9_of_forall_restriction`: `Annihilation07Q9` descends along an open covering
    of `X`, for any family of triangulated functors to the localized sheaf categories computing
    the restricted cohomology.
  * `annihilation07Q9_of_forall_opensOverRestriction`: the same descent for the derived
    restriction functors.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Tag 0159](https://stacks.math.columbia.edu/tag/0159)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
  TopologicalSpace Opposite

universe w w' w'' v₁ v₂ u₁ u₂ u

noncomputable section

/-! ### An exact functor on bounded below derived categories -/

namespace Stacks.ExactDerivedPlus

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **The action of an exact functor on bounded below derived categories commutes with the
shift.** -/
@[instance_reducible]
def commShiftMapDerivedCategoryPlus : F.mapDerivedCategoryPlus.CommShift ℤ :=
  Functor.commShiftOfLocalization DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso A) ℤ
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) F.mapDerivedCategoryPlus

attribute [local instance] commShiftMapDerivedCategoryPlus

/-- The degreewise description of the bounded below derived action of an exact functor is
compatible with the shift, for the commutation of `commShiftMapDerivedCategoryPlus`. -/
theorem natTransCommShift_mapDerivedCategoryPlusFactorsh :
    NatTrans.CommShift F.mapDerivedCategoryPlusFactorsh.hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso A) ℤ
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) F.mapDerivedCategoryPlus

attribute [local instance] natTransCommShift_mapDerivedCategoryPlusFactorsh

/-- **An exact functor acts triangulatedly on bounded below derived categories.** -/
theorem isTriangulated_mapDerivedCategoryPlus : F.mapDerivedCategoryPlus.IsTriangulated :=
  have : (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).IsTriangulated :=
    Functor.IsTriangulated.instComp _ _
  Functor.isTriangulated_of_precomp_iso F.mapDerivedCategoryPlusFactorsh

/-- **An exact functor commutes with the cohomology objects of the bounded below derived
category**: `ℋ^j(F_{D⁺}K) ≅ F(ℋ^j K)`. -/
def mapDerivedCategoryPlusHomologyIso (j : ℤ) (K : DerivedCategory.Plus A) :
    (DerivedCategory.Plus.homologyFunctor B j).obj (F.mapDerivedCategoryPlus.obj K) ≅
      F.obj ((DerivedCategory.Plus.homologyFunctor A j).obj K) :=
  (F.mapDerivedCategoryHomologyIso j).app (DerivedCategory.Plus.ι.obj K)

end Stacks.ExactDerivedPlus

/-! ### The conclusion of [Stacks, Tag 07Q9] in an arbitrary derived category -/

namespace Stacks.Triangulated

/-- For a morphism `α` of `D⁺(𝒜)`: in every distinguished triangle `A ⟶ B ⟶ E ⟶ A⟦1⟧` on `α`,
the cohomology objects of `E` are annihilated by `q`. -/
def ConeHomologyAnnihilation (𝒜 : Type u₁) [Category.{v₁} 𝒜] [Abelian 𝒜]
    [HasDerivedCategory.{w} 𝒜] (q : ℕ) {A B : DerivedCategory.Plus 𝒜} (α : A ⟶ B) : Prop :=
  ∀ (E : DerivedCategory.Plus 𝒜) (v : B ⟶ E) (wE : E ⟶ A⟦(1 : ℤ)⟧),
    Triangle.mk α v wE ∈ distTriang (DerivedCategory.Plus 𝒜) →
      ∀ j : ℤ, (q : ℤ) • 𝟙 ((DerivedCategory.Plus.homologyFunctor 𝒜 j).obj E) = 0

section ConeHomology

variable (𝒜 : Type u₁) [Category.{v₁} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- If two distinguished triangles have isomorphic first two objects, compatibly with the first
morphisms, and `q` annihilates the cohomology of the third object of the second one, then it
annihilates the cohomology of the third object of the first one. -/
private theorem smul_id_homology_eq_zero_of_distTriang {T T' : Triangle (DerivedCategory.Plus 𝒜)}
    (hT : T ∈ distTriang (DerivedCategory.Plus 𝒜)) (hT' : T' ∈ distTriang (DerivedCategory.Plus 𝒜))
    (a : T.obj₁ ≅ T'.obj₁) (b : T.obj₂ ≅ T'.obj₂) (comm : T.mor₁ ≫ b.hom = a.hom ≫ T'.mor₁)
    (q : ℤ) (j : ℤ) (h : q • 𝟙 ((DerivedCategory.Plus.homologyFunctor 𝒜 j).obj T'.obj₃) = 0) :
    q • 𝟙 ((DerivedCategory.Plus.homologyFunctor 𝒜 j).obj T.obj₃) = 0 :=
  Stacks.Algebraization.smul_id_eq_zero_of_iso q
    ((DerivedCategory.Plus.homologyFunctor 𝒜 j).mapIso
      (Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T T' hT hT' a b comm))) h

/-- **One distinguished triangle suffices.**  `ConeHomologyAnnihilation` holds as soon as one
cone of `α` has its cohomology objects annihilated by `q`. -/
theorem coneHomologyAnnihilation_iff_of_distTriang (q : ℕ)
    {A B E₀ : DerivedCategory.Plus 𝒜} (α : A ⟶ B) (v₀ : B ⟶ E₀) (w₀ : E₀ ⟶ A⟦(1 : ℤ)⟧)
    (hT₀ : Triangle.mk α v₀ w₀ ∈ distTriang (DerivedCategory.Plus 𝒜)) :
    ConeHomologyAnnihilation 𝒜 q α ↔
      ∀ j : ℤ, (q : ℤ) • 𝟙 ((DerivedCategory.Plus.homologyFunctor 𝒜 j).obj E₀) = 0 :=
  ⟨fun h j ↦ h E₀ v₀ w₀ hT₀ j, fun h E v wE hT j ↦
    smul_id_homology_eq_zero_of_distTriang 𝒜 hT hT₀ (Iso.refl A) (Iso.refl B) (by simp) _ j (h j)⟩

/-- **`ConeHomologyAnnihilation` absorbs an isomorphism on the target side**: if it holds for `α`
and `e` is invertible, it holds for `α ≫ e`. -/
theorem coneHomologyAnnihilation_comp_isIso (q : ℕ) {A B B' : DerivedCategory.Plus 𝒜}
    (α : A ⟶ B) (e : B ⟶ B') [IsIso e] (h : ConeHomologyAnnihilation 𝒜 q α) :
    ConeHomologyAnnihilation 𝒜 q (α ≫ e) := by
  intro E v wE hT j
  obtain ⟨E₀, v₀, w₀, hT₀⟩ := distinguished_cocone_triangle α
  exact smul_id_homology_eq_zero_of_distTriang 𝒜 hT hT₀ (Iso.refl A) (asIso e).symm (by simp) _ j
    (h E₀ v₀ w₀ hT₀ j)

/-- **`ConeHomologyAnnihilation` absorbs an isomorphism on the source side**: if it holds for `α`
and `e` is invertible, it holds for `e ≫ α`. -/
theorem coneHomologyAnnihilation_isIso_comp (q : ℕ) {A' A B : DerivedCategory.Plus 𝒜}
    (e : A' ⟶ A) [IsIso e] (α : A ⟶ B) (h : ConeHomologyAnnihilation 𝒜 q α) :
    ConeHomologyAnnihilation 𝒜 q (e ≫ α) := by
  intro E v wE hT j
  obtain ⟨E₀, v₀, w₀, hT₀⟩ := distinguished_cocone_triangle α
  exact smul_id_homology_eq_zero_of_distTriang 𝒜 hT hT₀ (asIso e) (Iso.refl B) (by simp) _ j
    (h E₀ v₀ w₀ hT₀ j)

variable (ℬ : Type u₂) [Category.{v₂} ℬ] [Abelian ℬ] [HasDerivedCategory.{w'} ℬ]

/-- **`ConeHomologyAnnihilation` transports along a triangulated functor whose cohomology objects
are computed by an additive functor downstairs.**  If `ℋ^j(G K) ≅ R(ℋ^j K)` for an additive
`R : 𝒜 ⥤ ℬ`, then `q` annihilating the cohomology of a cone of `α` makes it annihilate the
cohomology of a cone of `G.map α`. The isomorphisms are not required to be natural. -/
theorem coneHomologyAnnihilation_map (q : ℕ) {A B : DerivedCategory.Plus 𝒜} {α : A ⟶ B}
    (G : DerivedCategory.Plus 𝒜 ⥤ DerivedCategory.Plus ℬ) [G.CommShift ℤ] [G.IsTriangulated]
    (R : 𝒜 ⥤ ℬ) [R.Additive]
    (e : ∀ (j : ℤ) (K : DerivedCategory.Plus 𝒜),
      (DerivedCategory.Plus.homologyFunctor ℬ j).obj (G.obj K) ≅
        R.obj ((DerivedCategory.Plus.homologyFunctor 𝒜 j).obj K))
    (h : ConeHomologyAnnihilation 𝒜 q α) :
    ConeHomologyAnnihilation ℬ q (G.map α) := by
  intro E' v' w' hT' j
  obtain ⟨E₀, v₀, w₀, hT₀⟩ := distinguished_cocone_triangle α
  have hdist : Triangle.mk (G.map α) (G.map v₀)
        (G.map w₀ ≫ (G.commShiftIso (1 : ℤ)).hom.app A) ∈
      distTriang (DerivedCategory.Plus ℬ) :=
    G.map_distinguished (Triangle.mk α v₀ w₀) hT₀
  have hR : (q : ℤ) • 𝟙 (R.obj ((DerivedCategory.Plus.homologyFunctor 𝒜 j).obj E₀)) = 0 := by
    rw [← R.map_id, ← R.map_zsmul, h E₀ v₀ w₀ hT₀ j, R.map_zero]
  exact smul_id_homology_eq_zero_of_distTriang ℬ hT' hdist (Iso.refl _) (Iso.refl _) (by simp) _ j
    (Stacks.Algebraization.smul_id_eq_zero_of_iso (q : ℤ) (e j E₀) hR)

end ConeHomology

end Stacks.Triangulated

namespace Crystalline.GlobalCrystallineSituation.SmallSite

attribute [local instance] Stacks.ExactDerivedPlus.commShiftMapDerivedCategoryPlus
  Stacks.ExactDerivedPlus.natTransCommShift_mapDerivedCategoryPlusFactorsh

/-- `Annihilation07Q9` is `Stacks.Triangulated.ConeHomologyAnnihilation` at the
abelian sheaves on the small Zariski site, on the nose. -/
theorem annihilation07Q9_eq_coneHomologyAnnihilation (S : GlobalCrystallineSituation.{u})
    [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})] (q : ℕ)
    {A B : DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})} (α : A ⟶ B) :
    Annihilation07Q9 S q α =
      Stacks.Triangulated.ConeHomologyAnnihilation
        (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) q α :=
  rfl

/-! ### Restriction of abelian sheaves to an open of `X` -/

section Restriction

variable (S : GlobalCrystallineSituation.{u})

/-- Abelian sheaves on the localized small Zariski site `(X_Zar)/U` admit sheafification at the
coefficient universe `u + 1`. -/
instance instHasSheafifyOpensOverAddCommGrpCat (U : S.X.Opens) :
    HasSheafify ((opensTopology S).over U) AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u} _

/-- **Restriction of abelian sheaves from `X_Zar` to the localized site at an open `U`**, along
`Over.forget U`: on sections it is `(M ∣_ U)(V) = M(V)` for `V` an open of `X` contained in
`U`. -/
abbrev opensOverRestriction (U : S.X.Opens) :
    Sheaf (opensTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf ((opensTopology S).over U) AddCommGrpCat.{u + 1} :=
  (opensTopology S).overPullback AddCommGrpCat.{u + 1} U

/-- Restriction to an open is additive. -/
instance additive_opensOverRestriction (U : S.X.Opens) :
    (opensOverRestriction S U).Additive where
  map_add := by intros; rfl

/-- **Restriction to an open is left exact.** -/
instance preservesFiniteLimits_opensOverRestriction (U : S.X.Opens) :
    PreservesFiniteLimits (opensOverRestriction S U) :=
  inferInstance

/-- **Restriction to an open is right exact.** -/
instance preservesFiniteColimits_opensOverRestriction (U : S.X.Opens) :
    PreservesFiniteColimits (opensOverRestriction S U) :=
  inferInstance

/-- If `q` annihilates the identity of the restriction of `M` to `U`, then it annihilates the
identity of `M(V)` for every open `V ≤ U`. -/
theorem smul_id_obj_eq_zero_of_smul_id_opensOverRestriction_eq_zero (U : S.X.Opens)
    (M : Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) (q : ℤ)
    (h : q • 𝟙 ((opensOverRestriction S U).obj M) = 0) (V : S.X.Opens) (hV : V ≤ U) :
    q • 𝟙 (M.obj.obj (op V)) = 0 :=
  congrArg (fun g : (opensOverRestriction S U).obj M ⟶ (opensOverRestriction S U).obj M ↦
    g.hom.app (op (Over.mk (homOfLE hV)))) h

end Restriction

/-! ### `q • 𝟙 M = 0` is local on `X` -/

section SheafLocality

variable (S : GlobalCrystallineSituation.{u})

/-- **A scalar annihilating the sections of an abelian sheaf over every open of a covering
annihilates the sheaf.**  Let `U` be a family of opens of `X` with `⨆ U i = ⊤` and suppose `q`
annihilates the identity of `M(V)` for every open `V` contained in some `U i`.  Then
`q • 𝟙 M = 0`. -/
theorem smul_id_eq_zero_of_forall_le (M : Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) (q : ℤ)
    {ι : Type*} (U : ι → S.X.Opens) (hU : (⨆ i, U i) = ⊤)
    (h : ∀ (i : ι) (V : S.X.Opens), V ≤ U i → q • 𝟙 (M.obj.obj (op V)) = 0) :
    q • 𝟙 M = 0 := by
  have hsec : ∀ (i : ι) (V : S.X.Opens), V ≤ U i → ∀ t : ToType (M.obj.obj (op V)), q • t = 0 :=
    fun i V hV t ↦ by simpa using ConcreteCategory.congr_hom (h i V hV) t
  refine Sheaf.hom_ext ?_
  ext V s
  show (AddCommGrpCat.Hom.hom ((q • 𝟙 (M.obj.obj V))) s) = _
  have hsheaf := TopCat.Sheaf.eq_of_locally_eq' (F := M) (fun i ↦ V.unop ⊓ U i) V.unop
    (fun _ ↦ homOfLE inf_le_left) (by rw [← inf_iSup_eq, hU, inf_top_eq]) (q • s) 0 ?_
  · simpa using hsheaf
  · intro i
    have hzero : (AddCommGrpCat.Hom.hom
        (M.obj.map (homOfLE (inf_le_left : V.unop ⊓ U i ≤ V.unop)).op)) (q • s) = 0 := by
      rw [map_zsmul]
      exact hsec i (V.unop ⊓ U i) inf_le_right _
    simpa using hzero

/-- **`q • 𝟙 M = 0` is local on `X`**, in the form that mentions the restriction functor: if `q`
annihilates the identity of the restriction of `M` to every member of an open covering of `X`,
it annihilates the identity of `M`. -/
theorem smul_id_eq_zero_of_forall_opensOverRestriction
    (M : Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) (q : ℤ)
    {ι : Type*} (U : ι → S.X.Opens) (hU : (⨆ i, U i) = ⊤)
    (h : ∀ i : ι, q • 𝟙 ((opensOverRestriction S (U i)).obj M) = 0) :
    q • 𝟙 M = 0 :=
  smul_id_eq_zero_of_forall_le S M q U hU fun i V hV ↦
    smul_id_obj_eq_zero_of_smul_id_opensOverRestriction_eq_zero S (U i) M q (h i) V hV

end SheafLocality

/-! ### The locality of [Stacks, Tag 07Q9] -/

section Locality

variable (S : GlobalCrystallineSituation.{u})
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})]

/-- **`Annihilation07Q9` descends along an open covering of `X`.**  Let `U` be a
family of opens covering `X`, and for each `i` let `G i` be a triangulated functor from
`D⁺(Ab(X_Zar))` to the bounded below derived category of the localized site at `U i` whose
cohomology objects are the restrictions of the cohomology sheaves. If each `(G i).map α`
satisfies the conclusion of [Stacks, Tag 07Q9] for `q`, then so does `α`. The isomorphisms `e`
are not required to be natural. -/
theorem annihilation07Q9_of_forall_restriction (q : ℕ)
    {A B : DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})} (α : A ⟶ B)
    {ι : Type*} (U : ι → S.X.Opens) (hU : (⨆ i, U i) = ⊤)
    [∀ i : ι, HasDerivedCategory.{w''}
      (Sheaf ((opensTopology S).over (U i)) AddCommGrpCat.{u + 1})]
    (G : ∀ i : ι, DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf ((opensTopology S).over (U i)) AddCommGrpCat.{u + 1}))
    [∀ i : ι, (G i).CommShift ℤ] [∀ i : ι, (G i).IsTriangulated]
    (e : ∀ (i : ι) (j : ℤ)
      (K : DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})),
      (DerivedCategory.Plus.homologyFunctor
          (Sheaf ((opensTopology S).over (U i)) AddCommGrpCat.{u + 1}) j).obj ((G i).obj K) ≅
        (opensOverRestriction S (U i)).obj ((DerivedCategory.Plus.homologyFunctor
          (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) j).obj K))
    (h : ∀ i : ι, Stacks.Triangulated.ConeHomologyAnnihilation
      (Sheaf ((opensTopology S).over (U i)) AddCommGrpCat.{u + 1}) q ((G i).map α)) :
    Annihilation07Q9 S q α := by
  obtain ⟨E₀, v₀, w₀, hT₀⟩ := distinguished_cocone_triangle α
  refine (annihilation07Q9_iff_of_distTriang S q α v₀ w₀ hT₀).2 fun j ↦
    smul_id_eq_zero_of_forall_opensOverRestriction S _ (q : ℤ) U hU fun i ↦ ?_
  have hdist : Triangle.mk ((G i).map α) ((G i).map v₀)
      ((G i).map w₀ ≫ ((G i).commShiftIso (1 : ℤ)).hom.app A) ∈
      distTriang (DerivedCategory.Plus
        (Sheaf ((opensTopology S).over (U i)) AddCommGrpCat.{u + 1})) :=
    (G i).map_distinguished (Triangle.mk α v₀ w₀) hT₀
  exact Stacks.Algebraization.smul_id_eq_zero_of_iso (q : ℤ) (e i j E₀).symm
    (h i _ _ _ hdist j)

/-- **The locality of [Stacks, Tag 07Q9] on `X`.**  If the conclusion of [Stacks, Tag 07Q9]
holds for the derived restriction of `α` to every member of an open covering of `X`, it holds for
`α`. -/
theorem annihilation07Q9_of_forall_opensOverRestriction (q : ℕ)
    {A B : DerivedCategory.Plus (Sheaf (opensTopology S) AddCommGrpCat.{u + 1})} (α : A ⟶ B)
    {ι : Type*} (U : ι → S.X.Opens) (hU : (⨆ i, U i) = ⊤)
    [∀ i : ι, HasDerivedCategory.{w''}
      (Sheaf ((opensTopology S).over (U i)) AddCommGrpCat.{u + 1})]
    (h : ∀ i : ι, Stacks.Triangulated.ConeHomologyAnnihilation
      (Sheaf ((opensTopology S).over (U i)) AddCommGrpCat.{u + 1}) q
        ((opensOverRestriction S (U i)).mapDerivedCategoryPlus.map α)) :
    Annihilation07Q9 S q α :=
  have : ∀ i : ι, (opensOverRestriction S (U i)).mapDerivedCategoryPlus.IsTriangulated :=
    fun _ ↦ Stacks.ExactDerivedPlus.isTriangulated_mapDerivedCategoryPlus _
  annihilation07Q9_of_forall_restriction S q α U hU
    (fun i ↦ (opensOverRestriction S (U i)).mapDerivedCategoryPlus)
    (fun _ j K ↦ Stacks.ExactDerivedPlus.mapDerivedCategoryPlusHomologyIso _ j K) h

end Locality

end Crystalline.GlobalCrystallineSituation.SmallSite

end
