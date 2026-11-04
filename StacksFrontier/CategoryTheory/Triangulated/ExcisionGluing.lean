module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Functor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Glueing objects along an excision square of triangulated categories

Consider pretriangulated categories `C`, `C_U`, `C_V`, `C_P` with exact restriction functors
`a_U : C ⥤ C_U`, `a_V : C ⥤ C_V`, `b_U : C_U ⥤ C_P`, `b_V : C_V ⥤ C_P` and right adjoints
`R_U ⊣`, `R_V ⊣`, `S_V ⊣` of `a_U`, `a_V`, `b_V`. Think of an elementary distinguished square
`(U ⊆ W, j : V ⟶ W)` of algebraic spaces with `P = U ×_W V`, of `C = D_QCoh(𝒪_W)` and so on, of
the restrictions and of the derived direct images. Assume:

* `a_U ⊣ R_U` and `b_V ⊣ S_V` have invertible counits (`U ⊆ W` and `P ⊆ V` are open immersions);
* base change: `a_V (R_U A) ≅ S_V (b_U A)`;
* the objects `N` of `C_V` with `b_V N = 0` satisfy `a_U (R_V N) = 0`, and the counit
  `a_V (R_V N) ⟶ N` is invertible at them (excision).

Then an object `A` of `C_U` and an object `B` of `C_V` with `b_U A ≅ b_V B` are the restrictions
of a single object of `C`. This is the first assertion of [Stacks, Tag 08HB] in the abstract.

## The construction

Let `B_T ⟶ B ⟶ S_V(b_V B) ⟶ B_T⟦1⟧` be a triangle on the unit of `b_V ⊣ S_V`; then `b_V B_T = 0`.
The object `E` is the fibre of the map `R_U A ⟶ (R_V B_T)⟦1⟧` adjoint to
`a_V(R_U A) ≅ S_V(b_U A) ≅ S_V(b_V B) ⟶ B_T⟦1⟧`. On `U` the term `R_V B_T` dies, so `a_U E ≅ A`.
On `V` the defining triangle becomes the triangle of `B`: its first term is `B_T` by excision,
its third is `S_V(b_V B)`, and the connecting maps agree by construction, so `a_V E ≅ B`.

## Main results

* `CategoryTheory.Pretriangulated.exists_glue_of_excision`: the glueing.
* `CategoryTheory.Pretriangulated.isIso_counit_of_isIso_unit`: the excision hypothesis on the
  counit of `a_V ⊣ R_V` follows from the corresponding statement for the unit of the left adjoint
  `j_! ⊣ a_V`, extension by zero.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated

namespace CategoryTheory.Pretriangulated

variable {C CU CV CP : Type*} [Category* C] [Category* CU] [Category* CV] [Category* CP]
  [Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  [Preadditive CU] [HasZeroObject CU] [HasShift CU ℤ] [∀ n : ℤ, (shiftFunctor CU n).Additive]
  [Pretriangulated CU]
  [Preadditive CV] [HasZeroObject CV] [HasShift CV ℤ] [∀ n : ℤ, (shiftFunctor CV n).Additive]
  [Pretriangulated CV]
  [Preadditive CP] [HasZeroObject CP] [HasShift CP ℤ] [∀ n : ℤ, (shiftFunctor CP n).Additive]
  [Pretriangulated CP]

/-- If the counit of `L ⊣ G` is invertible, so is `L` applied to the unit. -/
private theorem isIso_map_unit_of_isIso_counit {C' D' : Type*} [Category* C'] [Category* D']
    {L : C' ⥤ D'} {G : D' ⥤ C'} (adj : L ⊣ G) [IsIso adj.counit] (X : C') :
    IsIso (L.map (adj.unit.app X)) :=
  isIso_of_comp_hom_eq_id (adj.counit.app (L.obj X)) (adj.left_triangle_components X)

/-- If `L K` is zero, there are no nonzero maps from the shifts of `K` to a right adjoint image. -/
private theorem eq_zero_of_isZero_obj {L : C ⥤ CU} {G : CU ⥤ C} [L.CommShift ℤ]
    [L.IsTriangulated] (adj : L ⊣ G) {K : C} (hK : IsZero (L.obj K)) {Y : CU} (n : ℤ)
    (z : K⟦n⟧ ⟶ G.obj Y) : z = 0 := by
  have := adj.isRightAdjoint
  obtain ⟨w, rfl⟩ := (adj.homEquiv _ _).surjective z
  have hKn : IsZero (L.obj (K⟦n⟧)) :=
    ((shiftFunctor CU n).map_isZero hK).of_iso ((L.commShiftIso n).app K)
  rw [hKn.eq_of_src w 0, Adjunction.homEquiv_unit]
  simp

/-- **Glueing along an excision square.** Under the hypotheses of the module docstring, objects
`A` of `C_U` and `B` of `C_V` with isomorphic images in `C_P` are the restrictions of one object
of `C`. -/
theorem exists_glue_of_excision {aU : C ⥤ CU} {aV : C ⥤ CV} {bU : CU ⥤ CP} {bV : CV ⥤ CP}
    [aU.CommShift ℤ] [aU.IsTriangulated] [aV.CommShift ℤ] [aV.IsTriangulated]
    [bV.CommShift ℤ] [bV.IsTriangulated]
    {RU : CU ⥤ C} {RV : CV ⥤ C} {SV : CP ⥤ CV}
    (adjU : aU ⊣ RU) (adjV : aV ⊣ RV) (adjι : bV ⊣ SV)
    [IsIso adjU.counit] [IsIso adjι.counit]
    (β : ∀ A : CU, aV.obj (RU.obj A) ≅ SV.obj (bU.obj A))
    (hUV : ∀ N : CV, IsZero (bV.obj N) → IsZero (aU.obj (RV.obj N)))
    (hexc : ∀ N : CV, IsZero (bV.obj N) → IsIso (adjV.counit.app N))
    (A : CU) (B : CV) (c : bU.obj A ≅ bV.obj B) :
    ∃ E : C, Nonempty (aU.obj E ≅ A) ∧ Nonempty (aV.obj E ≅ B) := by
  let := adjV.rightAdjointCommShift ℤ
  have := adjV.commShift_of_leftAdjoint ℤ
  -- the triangle `B_T ⟶ B ⟶ S_V(b_V B) ⟶ B_T⟦1⟧`
  obtain ⟨Z, g₀, h₀, hT₀⟩ := distinguished_cocone_triangle (adjι.unit.app B)
  let TB := (Triangle.mk (adjι.unit.app B) g₀ h₀).invRotate
  have hTB : TB ∈ distTriang CV := inv_rot_of_distTriang _ hT₀
  let BT := TB.obj₁
  have hBT : IsZero (bV.obj BT) := by
    exact Triangle.isZero₁_of_isIso₂ _ (bV.map_distinguished _ hTB)
      (isIso_map_unit_of_isIso_counit adjι B)
  -- the connecting map and its adjoint
  let e₃ : aV.obj (RU.obj A) ≅ SV.obj (bV.obj B) := β A ≪≫ SV.mapIso c
  let dflat : aV.obj (RU.obj A) ⟶ BT⟦(1 : ℤ)⟧ := e₃.hom ≫ TB.mor₃
  let d' : RU.obj A ⟶ (RV.obj BT)⟦(1 : ℤ)⟧ :=
    adjV.homEquiv _ _ dflat ≫ (RV.commShiftIso (1 : ℤ)).hom.app BT
  obtain ⟨E, f, g, hE⟩ := distinguished_cocone_triangle₂ d'
  refine ⟨E, ⟨?_⟩, ⟨?_⟩⟩
  · -- on `U` the term `R_V B_T` dies
    have : IsIso (aU.map g) :=
      (Triangle.isZero₁_iff_isIso₂ _ (aU.map_distinguished _ hE)).1 (hUV BT hBT)
    have : IsIso (adjU.counit.app A) := NatIso.isIso_app_of_isIso adjU.counit _
    exact asIso (aU.map g) ≪≫ asIso (adjU.counit.app A)
  · -- on `V` the defining triangle is the triangle of `B`
    have := hexc BT hBT
    let T₁ := (aV.mapTriangle.obj (Triangle.mk f g d')).rotate.rotate
    let T₂ := TB.rotate.rotate
    have hT₁ : T₁ ∈ distTriang CV :=
      rot_of_distTriang _ (rot_of_distTriang _ (aV.map_distinguished _ hE))
    have hT₂ : T₂ ∈ distTriang CV := rot_of_distTriang _ (rot_of_distTriang _ hTB)
    have hsq : T₁.mor₁ ≫ (adjV.counit.app BT)⟦(1 : ℤ)⟧' = e₃.hom ≫ T₂.mor₁ := by
      have key := adjV.commShiftIso_hom_app_counit_app_shift (A := ℤ) 1 BT
      rw [Functor.commShiftIso_comp_hom_app] at key
      have h₁ : T₁.mor₁ = aV.map (adjV.homEquiv _ _ dflat) ≫
          aV.map ((RV.commShiftIso (1 : ℤ)).hom.app BT) ≫
            (aV.commShiftIso (1 : ℤ)).hom.app (RV.obj BT) := by
        dsimp [T₁, Functor.mapTriangle, d']
        rw [Functor.map_comp, Category.assoc]
        rfl
      have h₃ : aV.map (adjV.homEquiv _ _ dflat) ≫ adjV.counit.app (BT⟦(1 : ℤ)⟧) = dflat :=
        (adjV.homEquiv_counit (g := adjV.homEquiv _ _ dflat)).symm.trans
          ((adjV.homEquiv _ _).symm_apply_apply dflat)
      have h₂ : T₂.mor₁ = TB.mor₃ := rfl
      rw [h₁, h₂]
      calc (aV.map (adjV.homEquiv _ _ dflat) ≫ aV.map ((RV.commShiftIso (1 : ℤ)).hom.app BT) ≫
              (aV.commShiftIso (1 : ℤ)).hom.app (RV.obj BT)) ≫ (adjV.counit.app BT)⟦(1 : ℤ)⟧'
          = aV.map (adjV.homEquiv _ _ dflat) ≫ ((aV.map ((RV.commShiftIso (1 : ℤ)).hom.app BT) ≫
              (aV.commShiftIso (1 : ℤ)).hom.app (RV.obj BT)) ≫
                (adjV.counit.app BT)⟦(1 : ℤ)⟧') := by simp only [Category.assoc]
        _ = aV.map (adjV.homEquiv _ _ dflat) ≫ adjV.counit.app (BT⟦(1 : ℤ)⟧) :=
          congrArg (aV.map (adjV.homEquiv _ _ dflat) ≫ ·) key
        _ = e₃.hom ≫ TB.mor₃ := h₃
    have hεBT : IsIso (adjV.counit.app BT) := hexc BT hBT
    exact (shiftFunctor CV (1 : ℤ)).preimageIso (Triangle.π₃.mapIso
      (exists_iso_of_arrow_iso T₁ T₂ hT₁ hT₂ (Arrow.isoMk e₃
        ((shiftFunctor CV (1 : ℤ)).mapIso (@asIso _ _ _ _ _ hεBT)) hsq.symm)).choose)

omit [HasZeroObject C] [Pretriangulated C] in
/-- Morphisms from all shifts of `K` to `X` vanish, then so do morphisms from all shifts of `K`
to `X⟦1⟧`. -/
theorem hom_shift_one_eq_zero {K X : C} (h : ∀ (n : ℤ) (y : K⟦n⟧ ⟶ X), y = 0) (n : ℤ)
    (z : K⟦n⟧ ⟶ X⟦(1 : ℤ)⟧) : z = 0 := by
  let e1 : K⟦n⟧⟦(-1 : ℤ)⟧ ≅ K⟦n + -1⟧ := ((shiftFunctorAdd' C n (-1) (n + -1) rfl).app K).symm
  let e2 : X⟦(1 : ℤ)⟧⟦(-1 : ℤ)⟧ ≅ X :=
    (shiftFunctorCompIsoId C (1 : ℤ) (-1) (add_neg_cancel 1)).app X
  have h0 : e1.inv ≫ z⟦(-1 : ℤ)⟧' ≫ e2.hom = 0 := h _ _
  have h1 : z⟦(-1 : ℤ)⟧' = 0 := by simpa using congrArg (fun t => e1.hom ≫ t ≫ e2.inv) h0
  exact (shiftFunctor C (-1)).map_injective (by rw [h1, Functor.map_zero])

/-- **Generation after glueing.** In the setting of `exists_glue_of_excision`, let `G` generate
`C_U`, let `E` be an object of `C` whose restriction to `U` is `G ⊞ G⟦1⟧`, and let `K` be an
object of `C_V` restricting to zero on `P` which detects the objects of `C_V` restricting to zero
on `P`. Assume moreover that an object of `C` restricting to zero on `U` and on `V` is zero. Then
an object `M` of `C` with no nonzero morphisms from the shifts of `E`, and whose restriction to `V`
has no nonzero morphisms from the shifts of `K`, is zero. -/
theorem isZero_of_orthogonal_glue {aU : C ⥤ CU} {aV : C ⥤ CV} {bU : CU ⥤ CP} {bV : CV ⥤ CP}
    [aU.CommShift ℤ] [aU.IsTriangulated] [aV.CommShift ℤ] [aV.IsTriangulated]
    [bV.CommShift ℤ] [bV.IsTriangulated] [bU.PreservesZeroMorphisms]
    {RU : CU ⥤ C} {SV : CP ⥤ CV} (adjU : aU ⊣ RU) (adjι : bV ⊣ SV) [IsIso adjU.counit]
    (γ : aU ⋙ bU ≅ aV ⋙ bV) (β : ∀ A : CU, aV.obj (RU.obj A) ≅ SV.obj (bU.obj A))
    (hloc : ∀ N : C, IsZero (aU.obj N) → IsZero (aV.obj N) → IsZero N)
    (K : CV) (hK0 : IsZero (bV.obj K))
    (hdet : ∀ N : CV, IsZero (bV.obj N) → (∀ (n : ℤ) (x : K⟦n⟧ ⟶ N), x = 0) → IsZero N)
    (G : CU) (hG : ∀ A : CU, (∀ (n : ℤ) (x : G⟦n⟧ ⟶ A), x = 0) → IsZero A)
    (E : C) (eE : aU.obj E ≅ G ⊞ G⟦(1 : ℤ)⟧) (M : C)
    (hE : ∀ (n : ℤ) (x : E⟦n⟧ ⟶ M), x = 0) (hK : ∀ (n : ℤ) (y : K⟦n⟧ ⟶ aV.obj M), y = 0) :
    IsZero M := by
  let := adjU.rightAdjointCommShift ℤ
  have := adjU.commShift_of_leftAdjoint ℤ
  have := adjU.isRightAdjoint
  have := adjι.isRightAdjoint
  -- the unit at `M` becomes invertible on `U`
  have hη := isIso_map_unit_of_isIso_counit adjU M
  obtain ⟨N, g, h, hT⟩ := distinguished_cocone_triangle (adjU.unit.app M)
  have hNU : IsZero (aU.obj N) :=
    Triangle.isZero₃_of_isIso₁ _ (aU.map_distinguished _ hT) hη
  -- the cone also dies on `V`
  have hNV : IsZero (aV.obj N) := by
    refine hdet _ ((Functor.map_isZero bU hNU).of_iso (γ.symm.app N)) fun n y => ?_
    have h₃ : y ≫ (aV.mapTriangle.obj (Triangle.mk (adjU.unit.app M) g h)).mor₃ = 0 :=
      hom_shift_one_eq_zero hK n _
    obtain ⟨z, hz⟩ := Triangle.coyoneda_exact₃ _ (aV.map_distinguished _ hT) y h₃
    have hz0 : z = 0 := by
      refine (cancel_mono (β (aU.obj M)).hom).1 ?_
      exact (eq_zero_of_isZero_obj adjι hK0 n _).trans zero_comp.symm
    rw [hz, hz0]
    exact zero_comp
  -- so the unit is invertible
  have : IsIso (adjU.unit.app M) := (Triangle.isZero₃_iff_isIso₁ _ hT).1 (hloc N hNU hNV)
  -- and the restriction to `U` is right orthogonal to the shifts of `G`
  have hMU : IsZero (aU.obj M) := by
    refine hG _ fun n x => ?_
    let x' : (G ⊞ G⟦(1 : ℤ)⟧)⟦n⟧ ⟶ aU.obj M := (biprod.fst : G ⊞ G⟦(1 : ℤ)⟧ ⟶ G)⟦n⟧' ≫ x
    have hx : x = (biprod.inl : G ⟶ G ⊞ G⟦(1 : ℤ)⟧)⟦n⟧' ≫ x' := by
      simp only [x', ← Category.assoc, ← Functor.map_comp, biprod.inl_fst, Functor.map_id,
        Category.id_comp]
    let y : aU.obj (E⟦n⟧) ⟶ aU.obj M :=
      (aU.commShiftIso n).hom.app E ≫ (eE.hom)⟦n⟧' ≫ x'
    have hy : y = 0 := by
      have h0 : adjU.homEquiv _ _ y ≫ inv (adjU.unit.app M) = 0 := hE n _
      have h1 : adjU.homEquiv _ _ y = 0 := by
        simpa using congrArg (· ≫ adjU.unit.app M) h0
      exact (adjU.homEquiv _ _).injective (h1.trans (by simp [Adjunction.homEquiv_unit]))
    have hx' : x' = 0 := by
      have := congrArg (fun t => (eE.inv)⟦n⟧' ≫ (aU.commShiftIso n).inv.app E ≫ t) hy
      simp only [y, comp_zero] at this
      simpa [← Functor.map_comp_assoc] using this
    rw [hx, hx', comp_zero]
  exact (Functor.map_isZero RU hMU).of_iso (asIso (adjU.unit.app M))

/-- **The unit is invertible away from the support of `K`.** Let `L ⊣ G` with `L` exact and
invertible counit, and let `K` be an object killed by `L` which detects the objects killed by
`L`. Then the unit `E ⟶ G (L E)` is invertible at every `E` right orthogonal to the shifts of
`K`: its cone is killed by `L` and is right orthogonal to the shifts of `K`, since
`G (L E)` is. -/
theorem isIso_unit_of_rightOrthogonal {L : C ⥤ CU} {G : CU ⥤ C} [L.CommShift ℤ]
    [L.IsTriangulated] (adj : L ⊣ G) [IsIso adj.counit] (K : C) (hLK : IsZero (L.obj K))
    (hdet : ∀ N : C, IsZero (L.obj N) → (∀ (n : ℤ) (x : K⟦n⟧ ⟶ N), x = 0) → IsZero N)
    (E : C) (hE : ∀ (n : ℤ) (x : K⟦n⟧ ⟶ E), x = 0) : IsIso (adj.unit.app E) := by
  have := adj.isRightAdjoint
  have hη := isIso_map_unit_of_isIso_counit adj E
  obtain ⟨N, g, h, hT⟩ := distinguished_cocone_triangle (adj.unit.app E)
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1 (hdet N ?_ fun n y => ?_)
  · exact Triangle.isZero₃_of_isIso₁ _ (L.map_distinguished _ hT) hη
  · obtain ⟨z, hz⟩ := Triangle.coyoneda_exact₃ _ hT y (hom_shift_one_eq_zero hE n _)
    rw [hz, eq_zero_of_isZero_obj adj hLK n z]
    exact zero_comp

/-- **The counit of an adjunction is invertible at `N` exactly when the right adjoint is fully
faithful on the morphisms out of `N`**: `R.map : (N ⟶ M) → (R N ⟶ R M)` is bijective for every
`M`, since it is the adjunction bijection precomposed with the counit at `N`. -/
@[sga "4 IV 9.1.1" "more general"]
theorem _root_.CategoryTheory.Adjunction.isIso_counit_app_iff_bijective_map {C D : Type*}
    [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (N : D) :
    IsIso (adj.counit.app N) ↔ ∀ M : D, Function.Bijective (fun g : N ⟶ M => R.map g) := by
  have key : ∀ (M : D) (g : N ⟶ M), R.map g = adj.homEquiv _ _ (adj.counit.app N ≫ g) := by
    intro M g
    rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
      adj.right_triangle_components, Category.id_comp]
  constructor
  · intro h M
    have hpre : Function.Bijective (fun g : N ⟶ M => adj.counit.app N ≫ g) :=
      ⟨fun g₁ g₂ hg => (cancel_epi _).1 hg, fun f => ⟨inv (adj.counit.app N) ≫ f, by simp⟩⟩
    have : (fun g : N ⟶ M => R.map g) =
        (adj.homEquiv _ _) ∘ (fun g : N ⟶ M => adj.counit.app N ≫ g) := funext (key M)
    rw [this]
    exact (adj.homEquiv _ _).bijective.comp hpre
  · intro h
    obtain ⟨g, hg⟩ := (h (L.obj (R.obj N))).2 (adj.unit.app (R.obj N))
    have hg' : R.map g = adj.unit.app (R.obj N) := hg
    refine ⟨g, ?_, ?_⟩
    · apply (adj.homEquiv _ _).injective
      rw [← key, hg', Adjunction.homEquiv_unit]
      simp
    · apply (h N).1
      simp [hg']

/-- **Excision for the right adjoint from excision for the left adjoint.** Let
`s ⊣ a ⊣ R` be adjunctions and let `P` be a class of objects of the source of `s` such that
`a (R N)` lies in `P` whenever `N` does. If the unit
`M ⟶ a (s M)` of `s ⊣ a` is invertible at every `M` in `P`, then so is the counit
`a (R N) ⟶ N` of `a ⊣ R` at every `N` in `P`: postcomposition with that counit is bijective on
morphisms out of members of `P`, being the composite of the two adjunction bijections and of
precomposition with the unit. -/
theorem isIso_counit_of_isIso_unit {C D : Type*} [Category* C] [Category* D] {s : D ⥤ C}
    {a : C ⥤ D} {R : D ⥤ C} (adjS : s ⊣ a) (adjR : a ⊣ R) (P : ObjectProperty D)
    (hunit : ∀ M, P M → IsIso (adjS.unit.app M)) (hP : ∀ N, P N → P (a.obj (R.obj N)))
    (N : D) (hN : P N) : IsIso (adjR.counit.app N) := by
  have key : ∀ M, P M →
      Function.Bijective (fun f : M ⟶ a.obj (R.obj N) => f ≫ adjR.counit.app N) := by
    intro M hM
    have := hunit M hM
    have heq : (fun f : M ⟶ a.obj (R.obj N) => f ≫ adjR.counit.app N) =
        (fun h => adjS.unit.app M ≫ h) ∘ (adjR.homEquiv _ _).symm ∘ (adjS.homEquiv _ _).symm := by
      funext f
      simp only [Function.comp_apply, Adjunction.homEquiv_counit, Functor.map_comp]
      simp only [Category.assoc]
      rw [← Category.assoc (adjS.unit.app M), adjS.unit_naturality f, Category.assoc,
        ← Category.assoc (adjS.unit.app (a.obj (R.obj N))),
        adjS.right_triangle_components (R.obj N)]
      exact congrArg (f ≫ ·) (Category.id_comp _).symm
    rw [heq]
    refine Function.Bijective.comp ?_ (((adjR.homEquiv _ _).symm.bijective).comp
      (adjS.homEquiv _ _).symm.bijective)
    exact ⟨fun h₁ h₂ h => (cancel_epi (adjS.unit.app M)).1 h,
      fun y => ⟨inv (adjS.unit.app M) ≫ y, by simp⟩⟩
  obtain ⟨σ, hσ⟩ := (key N hN).2 (𝟙 N)
  have hσ' : σ ≫ adjR.counit.app N = 𝟙 N := hσ
  have h : (adjR.counit.app N ≫ σ) ≫ adjR.counit.app N = 𝟙 _ ≫ adjR.counit.app N := by
    rw [assoc, hσ']
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  exact ⟨σ, (key _ (hP N hN)).1 h, hσ⟩

end CategoryTheory.Pretriangulated
