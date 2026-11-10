module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.Functoriality.AffineChartMap

/-!
# Functoriality of the conormal algebra: gluing the chart maps

For a commutative square of schemes with immersions `i : Z ⟶ X` and `i' : Z' ⟶ X'`, this file
restricts the chart-level maps of `AffineChartMap` to sections of the conormal pieces over a pair
of opens `V ⊆ f⁻¹W` (`conormalChartHom`) and shows that the resulting local sections over the
affine charts covering `V` are compatible on overlaps (`conormalChartHom_compatible`), so that
they glue.  It also records the gluing of additive maps into a sheaf of abelian groups
(`gluingAddMonoidHom`).

## References

* [Stacks Project, Tag 0634](https://stacks.math.columbia.edu/tag/0634)
* [Stacks Project, Tag 0633](https://stacks.math.columbia.edu/tag/0633)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace TopologicalSpace.Opens

universe u

namespace AlgebraicGeometry

private theorem chartConormalMap_nested
    {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i'] (comm : f ≫ i' = i ≫ g)
    (U V : X.affineOpens) (U' V' : X'.affineOpens)
    (hVU : V.1 ≤ U.1) (hV'U' : V'.1 ≤ U'.1)
    (hGU : U.1 ≤ g ⁻¹ᵁ U'.1) (hGV : V.1 ≤ g ⁻¹ᵁ V'.1)
    (hZU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (hZV : IsClosedImmersion (i.resLE V.1 (i ⁻¹ᵁ V.1) le_rfl))
    (hZ'U' : IsClosedImmersion (i'.resLE U'.1 (i' ⁻¹ᵁ U'.1) le_rfl))
    (hZ'V' : IsClosedImmersion (i'.resLE V'.1 (i' ⁻¹ᵁ V'.1) le_rfl))
    (n : ℕ)
    (x : ((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.obj
      (op (i' ⁻¹ᵁ U'.1))) :
    ((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).val.map
        (homOfLE (show i ⁻¹ᵁ V.1 ≤ i ⁻¹ᵁ U.1 from fun _ hz => hVU hz)).op
        (chartConormalMap i i' f g comm U U' hGU hZU hZ'U'
          (square_chart_preimage_le i i' f g comm U.1 U'.1 hGU) n x) =
      chartConormalMap i i' f g comm V V' hGV hZV hZ'V'
        (square_chart_preimage_le i i' f g comm V.1 V'.1 hGV) n
        (((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.map
          (homOfLE (show i' ⁻¹ᵁ V'.1 ≤ i' ⁻¹ᵁ U'.1 from fun _ hz => hV'U' hz)).op x) := by
  exact chartConormalMap_restrict_both i i' f g comm U V U' V' hVU hV'U'
    hGU hGV hZU hZV hZ'U' hZ'V'
    (square_chart_preimage_le i i' f g comm U.1 U'.1 hGU)
    (square_chart_preimage_le i i' f g comm V.1 V'.1 hGV) n x

noncomputable def gluingAddMonoidHom
    {T : TopCat.{u}} (G : TopCat.Sheaf Ab.{u} T) (V : TopologicalSpace.Opens T)
    {ι : Type u} (U : ι → TopologicalSpace.Opens T) (iUV : ∀ i, U i ⟶ V)
    (hcover : V ≤ ⨆ i, U i) {A : Type u} [AddCommGroup A]
    (φ : ∀ i, A →+ G.1.obj (op (U i)))
    (hcompat : ∀ a, TopCat.Presheaf.IsCompatible G.1 U (fun i => φ i a)) :
    A →+ G.1.obj (op V) := by
  classical
  let hexists (a : A) := (G.existsUnique_gluing' U V iUV hcover
    (fun i => φ i a) (hcompat a)).exists
  let glue (a : A) : G.1.obj (op V) :=
    Classical.choose (hexists a)
  have hglue (a : A) (i : ι) : G.1.map (iUV i).op (glue a) = φ i a :=
    Classical.choose_spec (hexists a) i
  refine { toFun := glue, map_zero' := ?_, map_add' := ?_ }
  · obtain ⟨s, _, huniq⟩ := G.existsUnique_gluing' U V iUV hcover
      (fun i => φ i 0) (hcompat 0)
    have h₁ : glue 0 = s := huniq (glue 0) (hglue 0)
    have h₂ : 0 = s := huniq 0 (by
      intro i
      change (ConcreteCategory.hom (G.1.map (iUV i).op)) 0 = _
      rw [(ConcreteCategory.hom (G.1.map (iUV i).op)).map_zero, (φ i).map_zero])
    exact h₁.trans h₂.symm
  · intro a b
    obtain ⟨s, _, huniq⟩ := G.existsUnique_gluing' U V iUV hcover
      (fun i => φ i (a + b)) (hcompat (a + b))
    have h₁ : glue (a + b) = s := huniq (glue (a + b)) (hglue (a + b))
    have h₂ : glue a + glue b = s := huniq (glue a + glue b) (by
      intro i
      change (ConcreteCategory.hom (G.1.map (iUV i).op))
          (glue a + glue b) = _
      rw [(ConcreteCategory.hom (G.1.map (iUV i).op)).map_add,
        hglue, hglue, (φ i).map_add])
    exact h₁.trans h₂.symm

theorem gluingAddMonoidHom_map
    {T : TopCat.{u}} (G : TopCat.Sheaf Ab.{u} T) (V : TopologicalSpace.Opens T)
    {ι : Type u} (U : ι → TopologicalSpace.Opens T) (iUV : ∀ i, U i ⟶ V)
    (hcover : V ≤ ⨆ i, U i) {A : Type u} [AddCommGroup A]
    (φ : ∀ i, A →+ G.1.obj (op (U i)))
    (hcompat : ∀ a, TopCat.Presheaf.IsCompatible G.1 U (fun i => φ i a))
    (i : ι) (a : A) :
    G.1.map (iUV i).op (gluingAddMonoidHom G V U iUV hcover φ hcompat a) = φ i a := by
  classical
  let hexists (a : A) := (G.existsUnique_gluing' U V iUV hcover
    (fun i => φ i a) (hcompat a)).exists
  let glue (a : A) : G.1.obj (op V) := Classical.choose (hexists a)
  have hglue (a : A) (i : ι) : G.1.map (iUV i).op (glue a) = φ i a :=
    Classical.choose_spec (hexists a) i
  change G.1.map (iUV i).op (glue a) = φ i a
  exact hglue a i

theorem presheaf_map_comp_apply
    {T : TopCat.{u}} (F : TopCat.Presheaf Ab T)
    {U V W : TopologicalSpace.Opens T} (f : V ⟶ U) (g : W ⟶ V)
    (x : ToType (F.obj (op U))) :
    F.map g.op (F.map f.op x) = F.map (g ≫ f).op x := by
  calc
    F.map g.op (F.map f.op x) = (F.map (f.op ≫ g.op)).hom x := by
      rw [← AddCommGrpCat.comp_apply, ← F.map_comp]
    _ = F.map (g ≫ f).op x := by
      congr 1

theorem moduleMap_underlying_apply
    {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat}
    (M : PresheafOfModules R) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : M.obj U) :
    ConcreteCategory.hom (M.presheaf.map f) x = (M.map f).hom x :=
  PresheafOfModules.presheaf_map_apply_coe (M := M) f x

/-- Restriction of scalars along a ring homomorphism does not change the underlying type of a
module. -/
private theorem restrictScalars_obj_coe
    {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (M : ModuleCat S) :
    (↑((ModuleCat.restrictScalars f).obj M) : Type _) = M := rfl

noncomputable def conormalChartHom
    {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i'] (comm : f ≫ i' = i ≫ g)
    (V : Z.Opens) (W : Z'.Opens) (_hVW : V ≤ f ⁻¹ᵁ W) (n : ℕ)
    (j : ConormalChartIndex i i' f g V W) :
    ((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.obj (op W) →+
      ((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).val.obj
        (op (conormalChartOpen j)) := by
  let hZU := isClosedImmersion_resLE_of_le_coborderRange i j.U.1 j.source_coborder
  let hZ'U' := isClosedImmersion_resLE_of_le_coborderRange i' j.U'.1 j.target_coborder
  let hFU := square_chart_preimage_le i i' f g comm j.U.1 j.U'.1
    j.ambient_compatible
  let targetRestrict := ConcreteCategory.hom
    (((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.map
      (homOfLE j.target_subset).op) |>.toAddMonoidHom
  exact (chartConormalMap i i' f g comm j.U j.U' j.ambient_compatible
    hZU hZ'U' hFU n).comp targetRestrict

theorem conormalChartHom_apply
    {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i'] (comm : f ≫ i' = i ≫ g)
    (V : Z.Opens) (W : Z'.Opens) (hVW : V ≤ f ⁻¹ᵁ W) (n : ℕ)
    (j : ConormalChartIndex i i' f g V W)
    (a : ((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.obj (op W)) :
    conormalChartHom i i' f g comm V W hVW n j a =
      chartConormalMap i i' f g comm j.U j.U' j.ambient_compatible
        (isClosedImmersion_resLE_of_le_coborderRange i j.U.1 j.source_coborder)
        (isClosedImmersion_resLE_of_le_coborderRange i' j.U'.1 j.target_coborder)
        (square_chart_preimage_le i i' f g comm j.U.1 j.U'.1
          j.ambient_compatible) n
        (ConcreteCategory.hom
          (((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.map
            (homOfLE j.target_subset).op) a) := by
  rfl

-- Comparing restrictions on common affine refinements involves repeated module coercions.
theorem conormalChartHom_compatible
    {Z X Z' X' : Scheme.{u}}
    (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z ⟶ Z') (g : X ⟶ X')
    [IsImmersion i] [IsImmersion i'] (comm : f ≫ i' = i ≫ g)
    (V : Z.Opens) (W : Z'.Opens) (hVW : V ≤ f ⁻¹ᵁ W) (n : ℕ)
    (a : ((Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)).val.obj (op W)) :
    TopCat.Presheaf.IsCompatible
      ((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).val.presheaf
      (fun j : ConormalChartIndex i i' f g V W => conormalChartOpen j)
      (fun j => conormalChartHom i i' f g comm V W hVW n j a) := by
  classical
  intro j k
  -- The two chart descriptions agree after refining their common domain.
  let T := conormalChartOpen j ⊓ conormalChartOpen k
  let A : X.Opens := j.U.1 ⊓ k.U.1
  let A' : X'.Opens := j.U'.1 ⊓ k.U'.1
  let W₀ : Z'.Opens := i' ⁻¹ᵁ A'
  have hTA : T ≤ i ⁻¹ᵁ A := by
    intro z hz
    change i z ∈ j.U.1 ∧ i z ∈ k.U.1
    exact ⟨hz.1, hz.2⟩
  have hWA' : W₀ ≤ i' ⁻¹ᵁ A' := le_rfl
  have hW₀W : W₀ ≤ W := by
    intro z hz
    apply j.target_subset
    change i' z ∈ j.U'.1
    exact hz.1
  have hTW : T ≤ f ⁻¹ᵁ W₀ := by
    intro z hz
    change i' (f z) ∈ A'
    refine ⟨?_, ?_⟩
    · exact square_chart_preimage_le i i' f g comm j.U.1 j.U'.1
        j.ambient_compatible hz.1
    · exact square_chart_preimage_le i i' f g comm k.U.1 k.U'.1
        k.ambient_compatible hz.2
  let L := ConormalChartRefinement i i' f g T W₀ A A'
  have hcover : T ≤ ⨆ l : L, conormalChartRefinementOpen l :=
    conormalChartRefinement_cover i i' f g comm T W₀ A A' hTA hWA' hTW
  let G := (Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)
  let G' := (Stacks.Conormal.conormalAlgebra i').algebra.piece (n : ℤ)
  let G'Ab : TopCat.Sheaf Ab (TopCat.of Z') := ⟨G'.val.presheaf, G'.isSheaf⟩
  let G'P := G'.val.presheaf
  let φj := conormalChartHom i i' f g comm V W hVW n j a
  let φk := conormalChartHom i i' f g comm V W hVW n k a
  let GAb : TopCat.Sheaf Ab (TopCat.of Z) := ⟨G.val.presheaf, G.isSheaf⟩
  let GP := G.val.presheaf
  let rj : GP.obj (op T) :=
    GP.map (homOfLE inf_le_left).op φj
  let rk : GP.obj (op T) :=
    GP.map (homOfLE inf_le_right).op φk
  -- Compare both restrictions on the refining affine cover.
  have hlocal : ∀ l : L,
      GP.map (homOfLE (show conormalChartRefinementOpen l ≤ T from
        fun z hz => by
          change i z ∈ l.U.1 at hz
          exact ⟨(l.source_refines hz).1, (l.source_refines hz).2⟩)).op rj =
      GP.map (homOfLE (show conormalChartRefinementOpen l ≤ T from
        fun z hz => by
          change i z ∈ l.U.1 at hz
          exact ⟨(l.source_refines hz).1, (l.source_refines hz).2⟩)).op rk := by
    intro l
    let hj : l.U.1 ≤ j.U.1 := fun _ hz => (l.source_refines hz).1
    let hk : l.U.1 ≤ k.U.1 := fun _ hz => (l.source_refines hz).2
    let hj' : l.U'.1 ≤ j.U'.1 := fun _ hz => (l.target_refines hz).1
    let hk' : l.U'.1 ≤ k.U'.1 := fun _ hz => (l.target_refines hz).2
    let hjZ' : i' ⁻¹ᵁ l.U'.1 ≤ i' ⁻¹ᵁ j.U'.1 := fun _ hz => hj' hz
    let hkZ' : i' ⁻¹ᵁ l.U'.1 ≤ i' ⁻¹ᵁ k.U'.1 := fun _ hz => hk' hz
    have hgj : l.U.1 ≤ g ⁻¹ᵁ j.U'.1 := fun _ hz => j.ambient_compatible (hj hz)
    have hgk : l.U.1 ≤ g ⁻¹ᵁ k.U'.1 := fun _ hz => k.ambient_compatible (hk hz)
    have hZUj : IsClosedImmersion (i.resLE j.U.1 (i ⁻¹ᵁ j.U.1) le_rfl) :=
      isClosedImmersion_resLE_of_le_coborderRange i j.U.1 j.source_coborder
    have hZUk : IsClosedImmersion (i.resLE k.U.1 (i ⁻¹ᵁ k.U.1) le_rfl) :=
      isClosedImmersion_resLE_of_le_coborderRange i k.U.1 k.source_coborder
    have hZUl : IsClosedImmersion (i.resLE l.U (i ⁻¹ᵁ l.U.1) le_rfl) :=
      isClosedImmersion_resLE_of_le_coborderRange i l.U.1 l.source_coborder
    have hZ'j : IsClosedImmersion (i'.resLE j.U'.1 (i' ⁻¹ᵁ j.U'.1) le_rfl) :=
      isClosedImmersion_resLE_of_le_coborderRange i' j.U'.1 j.target_coborder
    have hZ'k : IsClosedImmersion (i'.resLE k.U'.1 (i' ⁻¹ᵁ k.U'.1) le_rfl) :=
      isClosedImmersion_resLE_of_le_coborderRange i' k.U'.1 k.target_coborder
    have hZ'l : IsClosedImmersion (i'.resLE l.U'.1 (i' ⁻¹ᵁ l.U'.1) le_rfl) :=
      isClosedImmersion_resLE_of_le_coborderRange i' l.U'.1 l.target_coborder
    let hFlj := square_chart_preimage_le i i' f g comm j.U.1 j.U'.1
      j.ambient_compatible
    let hFlk := square_chart_preimage_le i i' f g comm k.U.1 k.U'.1
      k.ambient_compatible
    let hFll := square_chart_preimage_le i i' f g comm l.U.1 l.U'.1
      l.ambient_compatible
    let mapL := chartConormalMap i i' f g comm l.U l.U' l.ambient_compatible
      hZUl hZ'l hFll n
    let xj : ToType (G'P.obj (op (i' ⁻¹ᵁ j.U'.1))) := ConcreteCategory.hom
      (G'P.map (homOfLE j.target_subset).op) a
    let xk : ToType (G'P.obj (op (i' ⁻¹ᵁ k.U'.1))) := ConcreteCategory.hom
      (G'P.map (homOfLE k.target_subset).op) a
    have hxjInput : xj = (G'.val.map (homOfLE j.target_subset).op).hom a := by
      dsimp [xj, G'P]
      exact moduleMap_underlying_apply G'.val (homOfLE j.target_subset).op a
    have hxkInput : xk = (G'.val.map (homOfLE k.target_subset).op).hom a := by
      dsimp [xk, G'P]
      exact moduleMap_underlying_apply G'.val (homOfLE k.target_subset).op a
    have hlW : i' ⁻¹ᵁ l.U'.1 ≤ W := le_trans l.target_subset hW₀W
    let xl : ToType (G'P.obj (op (i' ⁻¹ᵁ l.U'.1))) := ConcreteCategory.hom
      (G'P.map (homOfLE hlW).op) a
    have hxj : xl = ConcreteCategory.hom
        (G'P.map (homOfLE hjZ').op) xj := by
      have hcomp : (homOfLE j.target_subset).op ≫ (homOfLE hjZ').op =
          (homOfLE hlW).op := by apply Subsingleton.elim
      change (G'P.map (homOfLE hlW).op).hom a = _
      rw [← hcomp, G'P.map_comp]
      rfl
    have hxk : xl = ConcreteCategory.hom
        (G'P.map (homOfLE hkZ').op) xk := by
      have hcomp : (homOfLE k.target_subset).op ≫ (homOfLE hkZ').op =
          (homOfLE hlW).op := by apply Subsingleton.elim
      change (G'P.map (homOfLE hlW).op).hom a = _
      rw [← hcomp, G'P.map_comp]
      rfl
    have hjl := chartConormalMap_nested i i' f g comm j.U l.U j.U' l.U'
      hj hj' j.ambient_compatible l.ambient_compatible hZUj hZUl hZ'j hZ'l n xj
    have hkl := chartConormalMap_nested i i' f g comm k.U l.U k.U' l.U'
      hk hk' k.ambient_compatible l.ambient_compatible hZUk hZUl hZ'k hZ'l n xk
    have hJ := hjl.trans (congrArg mapL hxj.symm)
    have hK := hkl.trans (congrArg mapL hxk.symm)
    -- Convert the defining chart restrictions to those in `hlocal`.
    have hPT : conormalChartRefinementOpen l ≤ T := by
      intro z hz
      change i z ∈ l.U.1 at hz
      have hA : i z ∈ A := l.source_refines hz
      change i z ∈ j.U.1 ∧ i z ∈ k.U.1 at hA
      exact hA
    let hjT : conormalChartRefinementOpen l ≤ conormalChartOpen j := by
      intro z hz
      change i z ∈ l.U.1 at hz
      exact (l.source_refines hz).1
    let hkT : conormalChartRefinementOpen l ≤ conormalChartOpen k := by
      intro z hz
      change i z ∈ l.U.1 at hz
      exact (l.source_refines hz).2
    have hJmap :
        (homOfLE (show i ⁻¹ᵁ l.U.1 ≤ i ⁻¹ᵁ j.U.1 from fun _ hz => hj hz)).op =
          (homOfLE hjT).op := by
      apply Subsingleton.elim
    have hKmap :
        (homOfLE (show i ⁻¹ᵁ l.U.1 ≤ i ⁻¹ᵁ k.U.1 from fun _ hz => hk hz)).op =
          (homOfLE hkT).op := by
      apply Subsingleton.elim
    have hrestrictJ : GP.map (homOfLE hPT).op rj =
        GP.map (homOfLE hjT).op φj := by
      dsimp [rj]
      have hcomp : (homOfLE (show T ≤ conormalChartOpen j from inf_le_left)).op ≫
          (homOfLE hPT).op = (homOfLE hjT).op := by
        apply Subsingleton.elim
      calc
        _ = GP.map ((homOfLE (show T ≤ conormalChartOpen j from inf_le_left)).op ≫
            (homOfLE hPT).op) φj :=
          presheaf_map_comp_apply GP
            (homOfLE (show T ≤ conormalChartOpen j from inf_le_left))
            (homOfLE hPT) φj
        _ = _ := congrArg (fun f => GP.map f φj) hcomp
    have hrestrictK : GP.map (homOfLE hPT).op rk =
        GP.map (homOfLE hkT).op φk := by
      dsimp [rk]
      have hcomp : (homOfLE (show T ≤ conormalChartOpen k from inf_le_right)).op ≫
          (homOfLE hPT).op = (homOfLE hkT).op := by
        apply Subsingleton.elim
      calc
        _ = GP.map ((homOfLE (show T ≤ conormalChartOpen k from inf_le_right)).op ≫
            (homOfLE hPT).op) φk :=
          presheaf_map_comp_apply GP
            (homOfLE (show T ≤ conormalChartOpen k from inf_le_right))
            (homOfLE hPT) φk
        _ = _ := congrArg (fun f => GP.map f φk) hcomp
    dsimp only [φj] at hrestrictJ
    dsimp only [φk] at hrestrictK
    rw [conormalChartHom_apply] at hrestrictJ
    rw [conormalChartHom_apply] at hrestrictK
    rw [hxjInput] at hJ
    rw [hxkInput] at hK
    rw [hJmap] at hJ
    rw [hKmap] at hK
    exact hrestrictJ.trans (hJ.trans (hK.symm.trans hrestrictK.symm))
  -- The sheaf uniqueness property detects equality on the refining cover.
  let P := fun l : L => conormalChartRefinementOpen l
  let inc : ∀ l, P l ⟶ T := fun l => homOfLE (show P l ≤ T from fun z hz => by
    change i z ∈ l.U.1 at hz
    have hsrc := l.source_refines hz
    change i z ∈ j.U.1 ⊓ k.U.1 at hsrc
    exact hsrc)
  let ψ : ∀ l, GP.obj (op (P l)) := fun l => GP.map (inc l).op rj
  have hψ : TopCat.Presheaf.IsCompatible GP P ψ := by
    intro l m
    change GP.map (infLELeft (P l) (P m)).op (GP.map (inc l).op rj) =
      GP.map (infLERight (P l) (P m)).op (GP.map (inc m).op rj)
    have hcomp : (inc l).op ≫ (infLELeft (P l) (P m)).op =
        (inc m).op ≫ (infLERight (P l) (P m)).op := by
      apply Subsingleton.elim
    calc
      _ = (GP.map ((inc l).op ≫ (infLELeft (P l) (P m)).op)).hom rj := by
        rw [← ConcreteCategory.comp_apply, ← GP.map_comp]
      _ = (GP.map ((inc m).op ≫ (infLERight (P l) (P m)).op)).hom rj :=
        congrArg (fun q => (GP.map q).hom rj) hcomp
      _ = _ := by
        simp only [← ConcreteCategory.comp_apply, ← GP.map_comp]
  obtain ⟨s, hs, huniq⟩ := GAb.existsUnique_gluing' P T inc hcover ψ hψ
  have hj : rj = s := huniq rj (by intro l; rfl)
  have hk : rk = s := huniq rk (by intro l; rw [← hlocal l])
  exact hj.trans hk.symm

end AlgebraicGeometry

end
