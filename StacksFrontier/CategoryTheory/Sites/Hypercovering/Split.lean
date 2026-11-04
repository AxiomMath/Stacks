module

public import Mathlib.AlgebraicTopology.SimplicialObject.Split
public import Mathlib.AlgebraicTopology.SimplicialSet.Splitting
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Basic

/-!
# Split simplicial semi-representable objects

A simplicial object of `FormalCoproduct C` — a simplicial semi-representable object, `SR(C)` in
the source — is *split* when the morphism it assigns to every surjection of simplices is
componentwise an isomorphism; and it is enough to test the elementary degeneracies. The same
criterion holds in finitely truncated degrees, where being split means admitting a split
simplicial extension.

## Main definitions

* `IsTruncatedSplit`: a truncated simplicial semi-representable object admits a split
  simplicial extension restricting to it.

## Main results

* `split_iff_components_of_epi` is Tag 0DAU (1) iff (2): being split is equivalent to every
  surjection of simplices acting by componentwise isomorphisms.
* `components_of_epi_iff_components_of_degeneracy` is Tag 0DAU (2) iff (3): it suffices to test
  the elementary degeneracies.
* `truncated_split_iff_components_of_epi` and
  `truncated_components_of_epi_iff_components_of_degeneracy` are the same two equivalences in
  truncated degrees.

## Implementation notes

The site structure plays no role here; the statements are about an arbitrary category `C`. A
split truncated object is represented by a split simplicial extension rather than by a choice of
nondegenerate summands, which packages the usual truncated coproduct decomposition without
choosing it. The four results express (1) iff (2) and (2) iff (3) of the source, in all degrees
and in truncated degrees respectively.

For the forward directions the decomposition of a splitting is transported into the canonical
cofan of a formal coproduct (`splittingDecompositionIso`), whose naturality along a surjection
(`splittingDecompositionIso_naturality`) exhibits the component maps as isomorphisms. For the
converse in truncated degrees, `ExtensionData` records the data needed to build the split
extension — the summands, their inclusions and the degreewise decomposition isomorphisms — and
`extensionFunctor` assembles it into a simplicial object, with `extensionTruncationIso`
identifying its truncation with the given object.

The index type of the nondegenerate summands is read off from the simplicial set of indices
`componentIndexSSet`, whose splitting is Mathlib's `SSet.splitting`; this is what makes the
nondegenerate part of each degree available without a choice.

## References

* [Stacks Project, Tag 0DAU](https://stacks.math.columbia.edu/tag/0DAU)
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C]

private lemma bijective_f_of_isIso {X Y : FormalCoproduct.{w} C}
    (f : X ⟶ Y) [IsIso f] : Function.Bijective f.f :=
  Function.bijective_iff_has_inverse.2 ⟨(inv f).f, inv_f_f f, f_inv_f f⟩

private lemma isIso_φ_of_comm {X X' Y Y' : FormalCoproduct.{w} C}
    (e₁ : X ⟶ X') (e₂ : Y ⟶ Y') [IsIso e₁] [IsIso e₂] {f : X ⟶ Y} {g : X' ⟶ Y'}
    (w : e₁ ≫ g = f ≫ e₂) (hf : ∀ p, IsIso (f.φ p)) (i : X'.I) : IsIso (g.φ i) := by
  obtain ⟨p, rfl⟩ := (bijective_f_of_isIso e₁).2 i
  obtain ⟨hidx, hφ⟩ := (FormalCoproduct.hom_ext_iff' _ _).mp w p
  have hobj : Y'.obj ((e₁ ≫ g).f p) = Y'.obj ((f ≫ e₂).f p) := congrArg Y'.obj hidx
  have hφ' : (e₁ ≫ g).φ p ≫ eqToHom hobj = (f ≫ e₂).φ p := by
    have hp' : hobj = (by rw [hidx]) := Subsingleton.elim _ _
    simpa [Category.assoc, hp'] using hφ
  have := hf p
  have : IsIso ((e₁ ≫ g).φ p ≫ eqToHom hobj) := by
    rw [hφ']
    exact inferInstanceAs (IsIso (f.φ p ≫ e₂.φ (f.f p)))
  have : IsIso (e₁.φ p ≫ g.φ (e₁.f p)) :=
    IsIso.of_isIso_comp_right ((e₁ ≫ g).φ p) (eqToHom hobj)
  exact IsIso.of_isIso_comp_left (e₁.φ p) _

private lemma isIso_of_epi_of_injective {m n : SimplexCategory} (φ : m ⟶ n) [Epi φ]
    (h : Function.Injective φ.toOrderHom) : IsIso φ := by
  have := SimplexCategory.mono_iff_injective.2 h
  rw [SimplexCategory.isIso_iff_of_epi]
  exact le_antisymm (SimplexCategory.len_le_of_mono φ) (SimplexCategory.len_le_of_epi φ)

/-- Composing an isomorphic component with another one gives an isomorphic component. -/
private lemma isIso_φ_map_comp {J : Type*} [Category J] (K : Jᵒᵖ ⥤ FormalCoproduct.{w} C)
    {a b c : J} (σ : a ⟶ b) (ψ : b ⟶ c) (i : (K.obj (op c)).I)
    (h₁ : IsIso ((K.map ψ.op).φ i)) (h₂ : IsIso ((K.map σ.op).φ ((K.map ψ.op).f i))) :
    IsIso ((K.map (σ ≫ ψ).op).φ i) := by
  rw [op_comp, K.map_comp]
  have : IsIso ((K.map ψ.op).φ i ≫ (K.map σ.op).φ ((K.map ψ.op).f i)) := inferInstance
  simpa using this

private noncomputable def isoOfIsIso {X Y : C} (f : X ⟶ Y) (h : IsIso f) : X ≅ Y :=
  @asIso _ _ _ _ f h

private def componentIndexSSet (K : SimplicialObject (FormalCoproduct.{w} C)) : SSet.{w} where
  obj Δ := (K.obj Δ).I
  map f := ↾(K.map f).f
  map_id Δ := by
    ext i
    simp
  map_comp f g := by
    ext i
    simp

private noncomputable def componentIndexEquiv
    (K : SimplicialObject (FormalCoproduct.{w} C)) (Δ : SimplexCategoryᵒᵖ) :
    (Σ A : SimplicialObject.Splitting.IndexSet Δ,
      (componentIndexSSet K).nonDegenerate A.1.unop.len) ≃ (K.obj Δ).I :=
  Equiv.ofBijective _ ((Cofan.nonempty_isColimit_iff_bijective_fromSigma _).mp
    ⟨(componentIndexSSet K).splitting.isColimit Δ⟩)

private def nondegSummand (K : SimplicialObject (FormalCoproduct.{w} C)) (n : ℕ) :
    FormalCoproduct.{w} C :=
  ⟨(componentIndexSSet K).nonDegenerate n,
    fun i => (K.obj (op (SimplexCategory.mk n))).obj i.1⟩

private def nondegInclusion (K : SimplicialObject (FormalCoproduct.{w} C)) (n : ℕ) :
    nondegSummand K n ⟶ K.obj (op (SimplexCategory.mk n)) :=
  ⟨fun i => i.1, fun _ => 𝟙 _⟩

private def splittingDecompositionCofan {X : SimplicialObject (FormalCoproduct.{w} C)}
    (s : X.Splitting) (Δ : SimplexCategoryᵒᵖ) :
    Cofan (fun A : ULift (SimplicialObject.Splitting.IndexSet Δ) => s.N A.down.1.unop.len) :=
  FormalCoproduct.cofan (ULift (SimplicialObject.Splitting.IndexSet Δ))
    (fun A => s.N A.down.1.unop.len)

private noncomputable def splittingDecompositionCofanIsColimit
    {X : SimplicialObject (FormalCoproduct.{w} C)} (s : X.Splitting)
    (Δ : SimplexCategoryᵒᵖ) : IsColimit (Cofan.mk (X.obj Δ) fun A :
      ULift (SimplicialObject.Splitting.IndexSet Δ) => (s.cofan Δ).inj A.down) := by
  let c : Cofan (fun A : ULift (SimplicialObject.Splitting.IndexSet Δ) =>
      SimplicialObject.Splitting.summand s.N Δ A.down) :=
    Cofan.mk (X.obj Δ) fun A => (s.cofan Δ).inj A.down
  refine Cofan.IsColimit.mk c (fun t => s.desc Δ fun A => t.inj (ULift.up A)) ?_ ?_
  · intro t ⟨A⟩
    change (s.cofan Δ).inj A ≫ s.desc Δ (fun A => t.inj (ULift.up A)) = _
    exact s.ι_desc Δ (fun A => t.inj (ULift.up A)) A
  · intro t m hm
    apply (s.isColimit Δ).hom_ext
    intro A
    change (s.cofan Δ).inj A.as ≫ m =
      (s.cofan Δ).inj A.as ≫ s.desc Δ (fun A => t.inj (ULift.up A))
    rw [s.ι_desc Δ (fun A => t.inj (ULift.up A)) A.as]
    exact hm (ULift.up A.as)

private noncomputable def splittingDecompositionIso {X : SimplicialObject (FormalCoproduct.{w} C)}
    (s : X.Splitting) (Δ : SimplexCategoryᵒᵖ) :
    (splittingDecompositionCofan s Δ).pt ≅ X.obj Δ :=
  IsColimit.coconePointUniqueUpToIso
    (FormalCoproduct.isColimitCofan _ _) (splittingDecompositionCofanIsColimit s Δ)

private lemma splittingDecompositionIso_fac {X : SimplicialObject (FormalCoproduct.{w} C)}
    (s : X.Splitting) (Δ : SimplexCategoryᵒᵖ)
    (A : ULift (SimplicialObject.Splitting.IndexSet Δ)) :
    (splittingDecompositionCofan s Δ).inj A ≫ (splittingDecompositionIso s Δ).hom =
      (s.cofan Δ).inj A.down :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (FormalCoproduct.isColimitCofan _ _) (splittingDecompositionCofanIsColimit s Δ) ⟨A⟩

private def splittingCofanMap {X : SimplicialObject (FormalCoproduct.{w} C)}
  (s : X.Splitting) {m n : SimplexCategory} (φ : m ⟶ n) [Epi φ] :
    (splittingDecompositionCofan s (op n)).pt ⟶
      (splittingDecompositionCofan s (op m)).pt :=
  ⟨fun p => ⟨ULift.up (p.1.down.epiComp φ.op), p.2⟩, fun _ => 𝟙 _⟩

private lemma splittingDecompositionIso_naturality
    {X : SimplicialObject (FormalCoproduct.{w} C)} (s : X.Splitting)
    {m n : SimplexCategory} (φ : m ⟶ n) [Epi φ] :
    (splittingDecompositionIso s (op n)).hom ≫ X.map φ.op =
      splittingCofanMap s φ ≫ (splittingDecompositionIso s (op m)).hom := by
  apply (FormalCoproduct.isColimitCofan _ _).hom_ext
  intro A
  have h₁ := splittingDecompositionIso_fac s (op n) A.as
  have h₂ := s.cofan_inj_epi_naturality A.as.down φ.op
  have h₁' : (splittingDecompositionCofan s (op n)).inj A.as ≫
      (splittingDecompositionIso s (op n)).hom ≫ X.map φ.op =
      (s.cofan (op n)).inj A.as.down ≫ X.map φ.op := by
    simpa [Category.assoc] using congrArg (fun f => f ≫ X.map φ.op) h₁
  have h₂' : (s.cofan (op n)).inj A.as.down ≫ X.map φ.op =
      (splittingDecompositionCofan s (op m)).inj
        (ULift.up (A.as.down.epiComp φ.op)) ≫
          (splittingDecompositionIso s (op m)).hom := by
    rw [h₂]
    exact (splittingDecompositionIso_fac s (op m)
      (ULift.up (A.as.down.epiComp φ.op))).symm
  have h₃' : (splittingDecompositionCofan s (op m)).inj
        (ULift.up (A.as.down.epiComp φ.op)) ≫
          (splittingDecompositionIso s (op m)).hom =
      (splittingDecompositionCofan s (op n)).inj A.as ≫
        splittingCofanMap s φ ≫ (splittingDecompositionIso s (op m)).hom := by
    have hMap : (splittingDecompositionCofan s (op m)).inj
          (ULift.up (A.as.down.epiComp φ.op)) =
          (splittingDecompositionCofan s (op n)).inj A.as ≫ splittingCofanMap s φ := by
      have hindex : ((splittingDecompositionCofan s (op m)).inj
          (ULift.up (A.as.down.epiComp φ.op))).f =
        ((splittingDecompositionCofan s (op n)).inj A.as ≫ splittingCofanMap s φ).f := by
        funext x
        dsimp [splittingDecompositionCofan, splittingCofanMap, FormalCoproduct.cofan,
          CategoryStruct.comp, FormalCoproduct.category]
        rfl
      apply FormalCoproduct.hom_ext hindex
      intro x
      dsimp [splittingDecompositionCofan, splittingCofanMap, FormalCoproduct.cofan,
        CategoryStruct.comp, FormalCoproduct.category]
      simp only [SimplicialObject.Splitting.IndexSet.epiComp]
      rw [← eqToHom_refl ((s.N (unop A.as.down.1).len).obj x) rfl]
    rw [hMap]
    exact Category.assoc _ _ _
  exact h₁'.trans (h₂'.trans h₃')

private lemma truncated_epi_hom_surjective {r : ℕ}
    {a b : SimplexCategory.Truncated r} (f : a ⟶ b) [Epi f] :
    Function.Surjective f.hom.toOrderHom := by
  classical
  by_contra hsurj
  obtain ⟨j, hj⟩ : ∃ j, ∀ x, f.hom.toOrderHom x ≠ j := by
    simpa [Function.Surjective] using hsurj
  by_cases hb0 : b.obj.len = 0
  · exact hj 0 (Fin.ext (by omega))
  · have hr : 1 ≤ r := le_trans (Nat.one_le_iff_ne_zero.mpr hb0) b.property
    let g : b.obj ⟶ SimplexCategory.mk 1 := SimplexCategory.Hom.mk ⟨
      (fun x => if x < j then 0 else 1), by
        intro x y hxy
        by_cases hx : x < j <;> by_cases hy : y < j <;> simp [hx, hy]
        all_goals omega⟩
    let h : b.obj ⟶ SimplexCategory.mk 1 := SimplexCategory.Hom.mk ⟨
      (fun x => if x ≤ j then 0 else 1), by
        intro x y hxy
        by_cases hx : x ≤ j <;> by_cases hy : y ≤ j <;> simp [hx, hy]
        all_goals omega⟩
    let c : SimplexCategory.Truncated r := ⟨SimplexCategory.mk 1, hr⟩
    let g' : b ⟶ c := ObjectProperty.homMk g
    let h' : b ⟶ c := ObjectProperty.homMk h
    have hcomp : f.hom ≫ g = f.hom ≫ h := by
      ext x : 3
      simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
      have hne := hj x
      show (if f.hom.toOrderHom x < j then (0 : Fin 2) else 1) =
        (if f.hom.toOrderHom x ≤ j then (0 : Fin 2) else 1)
      by_cases hlt : f.hom.toOrderHom x < j
      · simp [hlt, le_of_lt hlt]
      · have hgt : j < f.hom.toOrderHom x :=
          lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
        simp [hlt, not_le_of_gt hgt]
    have hcat : f ≫ g' = f ≫ h' :=
      ObjectProperty.hom_ext (fun x : SimplexCategory => x.len ≤ r) hcomp
    have hgh : g' = h' := (cancel_epi f).1 hcat
    have hval := congrArg (fun q => q.hom.toOrderHom j) hgh
    change g.toOrderHom j = h.toOrderHom j at hval
    change (if j < j then (0 : Fin 2) else 1) =
      (if j ≤ j then (0 : Fin 2) else 1) at hval
    simp at hval

private lemma truncated_epi_components_of_degeneracies {r : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r)
    (h : ∀ (n : ℕ) (hn : n + 1 ≤ r) (j : Fin (n + 1))
      (i : (K.obj (op (⟨SimplexCategory.mk n,
        Nat.le_of_succ_le hn⟩ : SimplexCategory.Truncated r))).I),
      IsIso ((K.map (ObjectProperty.homMk (SimplexCategory.σ j) :
        (⟨SimplexCategory.mk (n + 1), hn⟩ : SimplexCategory.Truncated r) ⟶
        (⟨SimplexCategory.mk n, Nat.le_of_succ_le hn⟩ :
          SimplexCategory.Truncated r)).op).φ i)) :
    ∀ (d : ℕ) (hd : d ≤ r) (n : SimplexCategory.Truncated r)
      (φ : (⟨SimplexCategory.mk d, hd⟩ : SimplexCategory.Truncated r) ⟶ n)
      (_hφ : Epi φ) (i : (K.obj (op n)).I),
      IsIso ((K.map φ.op).φ i) := by
  intro d
  induction d with
  | zero =>
    intro hd n φ hφ i
    have : Epi φ.hom := SimplexCategory.epi_iff_surjective.2 (truncated_epi_hom_surjective φ)
    have : IsIso φ := (ObjectProperty.isIso_hom_iff φ).mp
      (isIso_of_epi_of_injective φ.hom fun x y _ => Subsingleton.elim (α := Fin 1) x y)
    infer_instance
  | succ d ih =>
    intro hd n φ hφ i
    have : Epi φ.hom := SimplexCategory.epi_iff_surjective.2 (truncated_epi_hom_surjective φ)
    by_cases hinj : Function.Injective φ.hom.toOrderHom
    · have : IsIso φ := (ObjectProperty.isIso_hom_iff φ).mp (isIso_of_epi_of_injective φ.hom hinj)
      infer_instance
    · obtain ⟨j, ψ, hfac⟩ := SimplexCategory.eq_σ_comp_of_not_injective φ.hom hinj
      let b : SimplexCategory.Truncated r := ⟨SimplexCategory.mk d,
        le_trans (Nat.le_succ d) hd⟩
      let σ : (⟨SimplexCategory.mk (d + 1), hd⟩ : SimplexCategory.Truncated r) ⟶ b :=
        ObjectProperty.homMk (SimplexCategory.σ j)
      let ψ' : b ⟶ n := ObjectProperty.homMk ψ
      have hfac' : φ = σ ≫ ψ' :=
        ObjectProperty.hom_ext (fun x : SimplexCategory => x.len ≤ r) hfac
      have : Epi ψ' := epi_of_epi_fac hfac'.symm
      rw [hfac']
      exact isIso_φ_map_comp K σ ψ' i (ih (le_trans (Nat.le_succ d) hd) n ψ' inferInstance i)
        (h d hd j _)

/-! The index simplicial set of a truncated formal coproduct, extended by its skeleton. -/

private def truncatedComponentIndexSet {r : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r) : SSet.Truncated.{w} r where
  obj A := (K.obj A).I
  map f := ↾(K.map f).f
  map_id A := by
    ext i
    simp
  map_comp f g := by
    ext i
    simp

private noncomputable def truncatedComponentIndexExtension {r : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r) : SSet.{w} :=
  (SSet.Truncated.sk r).obj (truncatedComponentIndexSet K)

private noncomputable def truncatedComponentIndexEquiv {r : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r) (n : ℕ) (hn : n ≤ r) :
    (K.obj (op (⟨SimplexCategory.mk n, hn⟩ : SimplexCategory.Truncated r))).I ≃
      (truncatedComponentIndexExtension K).obj (op (SimplexCategory.mk n)) := by
  let η := (SSet.skAdj r).unit.app (truncatedComponentIndexSet K)
  letI : IsIso ((SSet.skAdj r).unit) := SSet.Truncated.sk_coreflective r
  letI : IsIso η := by infer_instance
  refine Equiv.mk (η.app (op (⟨SimplexCategory.mk n, hn⟩ : SimplexCategory.Truncated r)))
    ((inv η).app (op (⟨SimplexCategory.mk n, hn⟩ : SimplexCategory.Truncated r))) ?_ ?_
  · intro x
    exact congrFun (congrArg (fun f => f.app
      (op (⟨SimplexCategory.mk n, hn⟩ : SimplexCategory.Truncated r)))
      (IsIso.hom_inv_id η)) x
  · intro x
    exact congrFun (congrArg (fun f => f.app
      (op (⟨SimplexCategory.mk n, hn⟩ : SimplexCategory.Truncated r)))
      (IsIso.inv_hom_id η)) x

private lemma truncatedComponentIndexEquiv_naturality {r : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r)
    {m n : ℕ} (hm : m ≤ r) (hn : n ≤ r)
    (f : op (⟨SimplexCategory.mk m, hm⟩ : SimplexCategory.Truncated r) ⟶
      op (⟨SimplexCategory.mk n, hn⟩ : SimplexCategory.Truncated r))
    (x : (K.obj (op (⟨SimplexCategory.mk m, hm⟩ : SimplexCategory.Truncated r))).I) :
    truncatedComponentIndexEquiv K n hn ((K.map f).f x) =
      (truncatedComponentIndexExtension K).map
        ((SimplexCategory.Truncated.inclusion r).op.map f)
        (truncatedComponentIndexEquiv K m hm x) := by
  dsimp [truncatedComponentIndexEquiv, truncatedComponentIndexExtension,
    truncatedComponentIndexSet]
  exact congrArg (fun g => g x)
    (((SSet.skAdj r).unit.app (truncatedComponentIndexSet K)).naturality f)

private noncomputable def truncatedNondegSummand {r : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r) (n : ℕ) (hn : n ≤ r) :
    FormalCoproduct.{w} C where
  I := (truncatedComponentIndexExtension K).nonDegenerate n
  obj x := (K.obj (op (⟨SimplexCategory.mk n, hn⟩ : SimplexCategory.Truncated r))).obj
    ((truncatedComponentIndexEquiv K n hn).symm x.1)

private noncomputable def truncatedNondegInclusion {r : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r) (n : ℕ) (hn : n ≤ r) :
    truncatedNondegSummand K n hn ⟶
      K.obj (op (⟨SimplexCategory.mk n, hn⟩ : SimplexCategory.Truncated r)) :=
  ⟨fun x => (truncatedComponentIndexEquiv K n hn).symm x.1, fun _ => 𝟙 _⟩

private noncomputable def truncatedComponentDecompositionEquiv {r : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r) (n : ℕ) (_hn : n ≤ r) :
    (Σ A : SimplicialObject.Splitting.IndexSet (op (SimplexCategory.mk n)),
      (truncatedComponentIndexExtension K).nonDegenerate A.1.unop.len) ≃
      (truncatedComponentIndexExtension K).obj (op (SimplexCategory.mk n)) :=
  Equiv.ofBijective _ ((Cofan.nonempty_isColimit_iff_bijective_fromSigma _).mp
    ⟨(truncatedComponentIndexExtension K).splitting.isColimit (op (SimplexCategory.mk n))⟩)

private lemma truncatedComponentDecompositionEquiv_apply {r : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r) (n : ℕ) (hn : n ≤ r)
    (A : SimplicialObject.Splitting.IndexSet (op (SimplexCategory.mk n)))
    (x : (truncatedComponentIndexExtension K).nonDegenerate A.1.unop.len) :
    truncatedComponentDecompositionEquiv K n hn ⟨A, x⟩ =
      (truncatedComponentIndexExtension K).map A.e.op x.1 := by
  classical
  unfold truncatedComponentDecompositionEquiv
  dsimp only [Equiv.ofBijective]
  let J := truncatedComponentIndexExtension K
  show (J.splitting.cofan (op (SimplexCategory.mk n))).inj A x = _
  show (J.map A.e.op) x.1 = (J.map A.e.op) x.1
  rfl

private noncomputable def truncatedDecompositionIndexEquiv {r : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r) (n : ℕ) (hn : n ≤ r) :
    (Σ A : SimplicialObject.Splitting.IndexSet (op (SimplexCategory.mk n)),
      (truncatedComponentIndexExtension K).nonDegenerate A.1.unop.len) ≃
      (K.obj (op (⟨SimplexCategory.mk n, hn⟩ : SimplexCategory.Truncated r))).I :=
  (truncatedComponentDecompositionEquiv K n hn).trans (truncatedComponentIndexEquiv K n hn).symm

private lemma truncatedDecompositionIndexEquiv_apply {r : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r) (n : ℕ) (hn : n ≤ r)
    (A : SimplicialObject.Splitting.IndexSet (op (SimplexCategory.mk n)))
    (x : (truncatedComponentIndexExtension K).nonDegenerate A.1.unop.len) :
    truncatedDecompositionIndexEquiv K n hn ⟨A, x⟩ =
      (truncatedComponentIndexEquiv K n hn).symm
        ((truncatedComponentIndexExtension K).map A.e.op x.1) := by
  simp [truncatedDecompositionIndexEquiv, Equiv.trans_apply,
    truncatedComponentDecompositionEquiv_apply]

private lemma truncatedHomMkEpi {r : ℕ} {a b : SimplexCategory.Truncated r}
    (f : a.obj ⟶ b.obj) [Epi f] : Epi (ObjectProperty.homMk f : a ⟶ b) := by
  refine ⟨?_⟩
  intro Z g h gh
  apply ObjectProperty.hom_ext (fun x : SimplexCategory => x.len ≤ r)
  have gh' : f ≫ g.hom = f ≫ h.hom := congrArg (fun q => q.hom) gh
  exact (cancel_epi f).1 gh'

private structure ExtensionIndex (r : ℕ) (n : SimplexCategory) where
  vertex : SimplexCategory.Truncated r
  arrow : n ⟶ vertex.obj
  epi : Epi arrow := by infer_instance

attribute [local instance] ExtensionIndex.epi

private def extensionObject {r : ℕ}
    (N : SimplexCategory.Truncated r → FormalCoproduct.{w} C) (n : SimplexCategory) :
    FormalCoproduct.{w} C :=
  ⟨Σ A : ULift.{w} (ExtensionIndex r n), (N A.down.vertex).I,
    fun x => (N x.1.down.vertex).obj x.2⟩

private def extensionInclusion {r : ℕ}
    (N : SimplexCategory.Truncated r → FormalCoproduct.{w} C) {n : SimplexCategory}
    (A : ExtensionIndex r n) : N A.vertex ⟶ extensionObject N n :=
  ⟨fun x => ⟨⟨A⟩, x⟩, fun _ => 𝟙 _⟩

private def extensionDesc {r : ℕ}
    (N : SimplexCategory.Truncated r → FormalCoproduct.{w} C) {n : SimplexCategory}
    {Z : FormalCoproduct.{w} C} (f : ∀ A : ExtensionIndex r n, N A.vertex ⟶ Z) :
    extensionObject N n ⟶ Z :=
  ⟨fun x => (f x.1.down).f x.2, fun x => (f x.1.down).φ x.2⟩

private lemma extensionInclusion_desc {r : ℕ}
    (N : SimplexCategory.Truncated r → FormalCoproduct.{w} C) {n : SimplexCategory}
    {Z : FormalCoproduct.{w} C} (f : ∀ A : ExtensionIndex r n, N A.vertex ⟶ Z)
    (A : ExtensionIndex r n) : extensionInclusion N A ≫ extensionDesc N f = f A := by
  refine FormalCoproduct.hom_ext rfl ?_
  intro x
  show (𝟙 _ ≫ (f A).φ x) ≫ eqToHom _ = (f A).φ x
  simp

private lemma extension_hom_ext {r : ℕ}
    (N : SimplexCategory.Truncated r → FormalCoproduct.{w} C) {n : SimplexCategory}
    {Z : FormalCoproduct.{w} C} {f g : extensionObject N n ⟶ Z}
    (h : ∀ A, extensionInclusion N A ≫ f = extensionInclusion N A ≫ g) : f = g := by
  have hi : f.f = g.f := by
    funext ⟨⟨A⟩, x⟩
    exact congrArg (fun q => q.f x) (h A)
  apply FormalCoproduct.hom_ext hi
  rintro ⟨⟨A⟩, x⟩
  have hφ := ((FormalCoproduct.hom_ext_iff' _ _).mp (h A) x).2
  change (𝟙 _ ≫ f.φ ⟨⟨A⟩, x⟩) ≫ eqToHom _ =
    𝟙 _ ≫ g.φ ⟨⟨A⟩, x⟩ at hφ
  simpa only [Category.id_comp] using hφ

private def extensionRaise {r : ℕ}
    (N : SimplexCategory.Truncated r → FormalCoproduct.{w} C)
    {m n : SimplexCategory} (e : m ⟶ n) [Epi e] :
    extensionObject N n ⟶ extensionObject N m :=
  ⟨fun x => ⟨⟨⟨x.1.down.vertex, e ≫ x.1.down.arrow, inferInstance⟩⟩, x.2⟩, fun _ => 𝟙 _⟩

private lemma extensionInclusion_raise {r : ℕ}
    (N : SimplexCategory.Truncated r → FormalCoproduct.{w} C)
    {m n : SimplexCategory} (e : m ⟶ n) [Epi e] (A : ExtensionIndex r n) :
    extensionInclusion N A ≫ extensionRaise N e =
      extensionInclusion N ⟨A.vertex, e ≫ A.arrow, inferInstance⟩ := by
  refine FormalCoproduct.hom_ext rfl ?_
  intro x
  show (𝟙 _ ≫ 𝟙 _) ≫ eqToHom _ = 𝟙 _
  simp

private lemma extensionInclusion_congr {r : ℕ}
    (N : SimplexCategory.Truncated r → FormalCoproduct.{w} C)
    {n : SimplexCategory} {a : SimplexCategory.Truncated r}
    {e f : n ⟶ a.obj} [Epi e] [Epi f] (h : e = f) :
    extensionInclusion N ⟨a, e, inferInstance⟩ =
      extensionInclusion N ⟨a, f, inferInstance⟩ := by
  subst f
  rfl

private lemma extensionRaise_comp {r : ℕ}
    (N : SimplexCategory.Truncated r → FormalCoproduct.{w} C)
    {l m n : SimplexCategory} (e : l ⟶ m) [Epi e] (f : m ⟶ n) [Epi f] :
    extensionRaise N (e ≫ f) = extensionRaise N f ≫ extensionRaise N e := by
  apply extension_hom_ext N
  intro A
  rw [← Category.assoc, extensionInclusion_raise, extensionInclusion_raise,
    extensionInclusion_raise]
  exact extensionInclusion_congr N (Category.assoc _ _ _)

private lemma extensionRaise_id {r : ℕ}
    (N : SimplexCategory.Truncated r → FormalCoproduct.{w} C) (n : SimplexCategory) :
    extensionRaise N (𝟙 n) = 𝟙 _ := by
  apply extension_hom_ext N
  intro A
  rw [extensionInclusion_raise, Category.comp_id]
  cases A
  exact extensionInclusion_congr N (Category.id_comp _)

private abbrev truncatedMap {r : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r)
    {a b : SimplexCategory.Truncated r} (f : a.obj ⟶ b.obj) :=
  K.map (ObjectProperty.homMk f : a ⟶ b).op

private lemma truncatedMap_comp {r : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r)
    {a b c : SimplexCategory.Truncated r} (f : a.obj ⟶ b.obj) (g : b.obj ⟶ c.obj) :
    truncatedMap K (a := a) (b := c) (f ≫ g) =
      truncatedMap K (a := b) (b := c) g ≫ truncatedMap K (a := a) (b := b) f :=
  K.map_comp (ObjectProperty.homMk g : b ⟶ c).op
    (ObjectProperty.homMk f : a ⟶ b).op

/-- A coproduct decomposition in the truncated degrees, with its canonical maps. -/
private structure ExtensionData {r : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r) where
  N : SimplexCategory.Truncated r → FormalCoproduct.{w} C
  ι : ∀ a, N a ⟶ K.obj (op a)
  iso : ∀ a, extensionObject N a.obj ≅ K.obj (op a)
  fac : ∀ a (A : ExtensionIndex r a.obj),
    extensionInclusion N A ≫ (iso a).hom =
      ι A.vertex ≫ truncatedMap K (a := a) A.arrow

private lemma extensionData_epi_naturality {r : ℕ}
    {K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r} (d : ExtensionData K)
    {a b : SimplexCategory.Truncated r} (e : a.obj ⟶ b.obj) [Epi e] :
    (d.iso b).hom ≫ truncatedMap K (a := a) (b := b) e =
      extensionRaise d.N e ≫ (d.iso a).hom := by
  apply extension_hom_ext d.N
  intro A
  rw [← Category.assoc, d.fac, Category.assoc, ← truncatedMap_comp,
    ← Category.assoc, extensionInclusion_raise, d.fac]

/-- Factor an operator through a degree within the truncation, then use the
coproduct decomposition to extend its degeneracy part. -/
private noncomputable def extensionTransition {r : ℕ}
    {K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r} (d : ExtensionData K)
    {n : SimplexCategory} {a : SimplexCategory.Truncated r} (f : n ⟶ a.obj) :
    K.obj (op a) ⟶ extensionObject d.N n :=
  let b : SimplexCategory.Truncated r :=
    ⟨image f, (SimplexCategory.len_le_of_mono (image.ι f)).trans a.property⟩
  truncatedMap K (a := b) (b := a) (image.ι f) ≫
    (d.iso b).inv ≫ extensionRaise d.N (factorThruImage f)

private lemma extensionTransition_factor {r : ℕ}
    {K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r} (d : ExtensionData K)
    {n : SimplexCategory} {a b : SimplexCategory.Truncated r} (f : n ⟶ a.obj)
    (e : n ⟶ b.obj) [Epi e] (i : b.obj ⟶ a.obj) [Mono i] (fac : e ≫ i = f) :
    extensionTransition d (a := a) f =
      truncatedMap K (a := b) (b := a) i ≫ (d.iso b).inv ≫ extensionRaise d.N e := by
  rcases b with ⟨b, hb⟩
  have hb' := SimplexCategory.image_eq fac
  dsimp at hb'
  subst b
  dsimp only [extensionTransition]
  simp only [SimplexCategory.factorThruImage_eq fac, SimplexCategory.image_ι_eq fac]

private lemma extensionTransition_epi_comp {r : ℕ}
    {K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r} (d : ExtensionData K)
    {m n : SimplexCategory} {a : SimplexCategory.Truncated r}
    (e : m ⟶ n) [Epi e] (f : n ⟶ a.obj) :
    extensionTransition d (a := a) (e ≫ f) =
      extensionTransition d (a := a) f ≫ extensionRaise d.N e := by
  let b : SimplexCategory.Truncated r :=
    ⟨image f, (SimplexCategory.len_le_of_mono (image.ι f)).trans a.property⟩
  rw [extensionTransition_factor d (b := b) (e ≫ f)
    (e ≫ factorThruImage f) (image.ι f) (by simp), extensionRaise_comp]
  simp only [extensionTransition, Category.assoc]
  rfl

private lemma extensionTransition_low {r : ℕ}
    {K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r} (d : ExtensionData K)
    {a b : SimplexCategory.Truncated r} (f : a.obj ⟶ b.obj) :
    extensionTransition d (a := b) f =
      truncatedMap K (a := a) (b := b) f ≫ (d.iso a).inv := by
  let c : SimplexCategory.Truncated r :=
    ⟨image f, (SimplexCategory.len_le_of_mono (image.ι f)).trans b.property⟩
  have he := extensionData_epi_naturality d (a := a) (b := c) (factorThruImage f)
  have he' : (d.iso c).inv ≫ extensionRaise d.N (factorThruImage f) =
      truncatedMap K (a := a) (b := c) (factorThruImage f) ≫ (d.iso a).inv := by
    rw [← cancel_mono (d.iso a).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← he, Iso.inv_hom_id_assoc]
  show truncatedMap K (a := c) (b := b) (image.ι f) ≫
    (d.iso c).inv ≫ extensionRaise d.N (factorThruImage f) = _
  rw [he', ← Category.assoc, ← truncatedMap_comp, image.fac]

private lemma extensionTransition_comp_low {r : ℕ}
    {K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r} (d : ExtensionData K)
    {n : SimplexCategory} {a b : SimplexCategory.Truncated r}
    (f : n ⟶ a.obj) (g : a.obj ⟶ b.obj) :
    extensionTransition d (a := b) (f ≫ g) =
      truncatedMap K (a := a) (b := b) g ≫ extensionTransition d (a := a) f := by
  let c : SimplexCategory.Truncated r :=
    ⟨image f, (SimplexCategory.len_le_of_mono (image.ι f)).trans a.property⟩
  conv_lhs => rw [← image.fac f, Category.assoc]
  rw [extensionTransition_epi_comp, extensionTransition_low d (a := c),
    truncatedMap_comp K (a := c) (b := a) (c := b)]
  simp only [Category.assoc]
  rfl

private noncomputable def extensionMap {r : ℕ}
    {K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r} (d : ExtensionData K)
    {m n : SimplexCategory} (f : m ⟶ n) :
    extensionObject d.N n ⟶ extensionObject d.N m :=
  extensionDesc d.N fun A => d.ι A.vertex ≫
    extensionTransition d (a := A.vertex) (f ≫ A.arrow)

private lemma extensionInclusion_map {r : ℕ}
    {K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r} (d : ExtensionData K)
    {m n : SimplexCategory} (f : m ⟶ n) (A : ExtensionIndex r n) :
    extensionInclusion d.N A ≫ extensionMap d f =
      d.ι A.vertex ≫ extensionTransition d (a := A.vertex) (f ≫ A.arrow) :=
  extensionInclusion_desc _ _ _

private lemma extensionMap_low {r : ℕ}
    {K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r} (d : ExtensionData K)
    {m : SimplexCategory} {a : SimplexCategory.Truncated r} (f : m ⟶ a.obj) :
    extensionMap d f = (d.iso a).hom ≫ extensionTransition d (a := a) f := by
  apply extension_hom_ext d.N
  intro A
  rw [extensionInclusion_map, ← Category.assoc, d.fac, Category.assoc,
    extensionTransition_comp_low]

private lemma extensionRaise_map {r : ℕ}
    {K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r} (d : ExtensionData K)
    {l m n : SimplexCategory} (f : l ⟶ m) (e : m ⟶ n) [Epi e] :
    extensionRaise d.N e ≫ extensionMap d f = extensionMap d (f ≫ e) := by
  apply extension_hom_ext d.N
  intro A
  rw [← Category.assoc, extensionInclusion_raise, extensionInclusion_map,
    extensionInclusion_map]
  simp only [Category.assoc]

private lemma extensionTransition_map {r : ℕ}
    {K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r} (d : ExtensionData K)
    {m n : SimplexCategory} {a : SimplexCategory.Truncated r}
    (f : m ⟶ n) (g : n ⟶ a.obj) :
    extensionTransition d (a := a) g ≫ extensionMap d f =
      extensionTransition d (a := a) (f ≫ g) := by
  let b : SimplexCategory.Truncated r :=
    ⟨image g, (SimplexCategory.len_le_of_mono (image.ι g)).trans a.property⟩
  show (truncatedMap K (a := b) (b := a) (image.ι g) ≫
    (d.iso b).inv ≫ extensionRaise d.N (factorThruImage g)) ≫ _ = _
  rw [Category.assoc, Category.assoc, extensionRaise_map, extensionMap_low d (a := b),
    Iso.inv_hom_id_assoc, ← extensionTransition_comp_low, Category.assoc, image.fac]

private lemma extensionMap_comp {r : ℕ}
    {K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r} (d : ExtensionData K)
    {l m n : SimplexCategory} (f : l ⟶ m) (g : m ⟶ n) :
    extensionMap d (f ≫ g) = extensionMap d g ≫ extensionMap d f := by
  apply extension_hom_ext d.N
  intro A
  rw [← Category.assoc, extensionInclusion_map, extensionInclusion_map,
    Category.assoc]
  rw [Category.assoc, extensionTransition_map]

private lemma extensionMap_epi {r : ℕ}
    {K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r} (d : ExtensionData K)
    {m n : SimplexCategory} (e : m ⟶ n) [Epi e] :
    extensionMap d e = extensionRaise d.N e := by
  apply extension_hom_ext d.N
  intro A
  rw [extensionInclusion_map, extensionInclusion_raise,
    extensionTransition_factor d (b := A.vertex) (e ≫ A.arrow)
      (e ≫ A.arrow) (𝟙 _) (Category.comp_id _)]
  show d.ι A.vertex ≫ K.map (𝟙 (op A.vertex)) ≫ (d.iso A.vertex).inv ≫ _ = _
  rw [K.map_id, Category.id_comp]
  have h := d.fac A.vertex (⟨A.vertex, 𝟙 _, inferInstance⟩)
  change extensionInclusion d.N (⟨A.vertex, 𝟙 _, inferInstance⟩) ≫ (d.iso A.vertex).hom =
    d.ι A.vertex ≫ K.map (𝟙 (op A.vertex)) at h
  rw [K.map_id, Category.comp_id] at h
  rw [← h, Category.assoc, Iso.hom_inv_id_assoc, extensionInclusion_raise]
  exact extensionInclusion_congr d.N (Category.comp_id _)

private noncomputable def extensionFunctor {r : ℕ}
    {K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r} (d : ExtensionData K) :
    SimplicialObject (FormalCoproduct.{w} C) where
  obj n := extensionObject d.N n.unop
  map f := extensionMap d f.unop
  map_id n := by rw [unop_id, extensionMap_epi, extensionRaise_id]
  map_comp f g := extensionMap_comp d g.unop f.unop

private noncomputable def extensionTruncationIso {r : ℕ}
    {K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r} (d : ExtensionData K) :
    (SimplicialObject.truncation r).obj (extensionFunctor d) ≅ K :=
  NatIso.ofComponents (fun a => d.iso a.unop) (by
    intro a b f
    change extensionMap d f.unop.hom ≫ (d.iso b.unop).hom =
      (d.iso a.unop).hom ≫ truncatedMap K (a := b.unop) (b := a.unop) f.unop.hom
    rw [extensionMap_low d (a := a.unop), extensionTransition_low d (a := b.unop)]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

private lemma isIso_of_bijective_components {X Y : FormalCoproduct.{w} C}
    (f : X ⟶ Y) (hf : Function.Bijective f.f) (h : ∀ i, IsIso (f.φ i)) : IsIso f := by
  let e := Equiv.ofBijective f.f hf
  let β := FormalCoproduct.isoOfComponents e (fun i => isoOfIsIso (f.φ i) (h i))
  have hβ : β.hom = f := by
    refine FormalCoproduct.hom_ext rfl ?_
    intro i
    show (asIso (f.φ i)).hom ≫ eqToHom _ = f.φ i
    simp
  rw [← hβ]
  infer_instance

private noncomputable abbrev truncatedSummands {r : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r)
    (a : SimplexCategory.Truncated r) := truncatedNondegSummand K a.obj.len a.property

private noncomputable abbrev truncatedSummandInclusion {r : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r)
    (a : SimplexCategory.Truncated r) := truncatedNondegInclusion K a.obj.len a.property

private noncomputable def extensionLowHom {r : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r)
    (a : SimplexCategory.Truncated r) :
    extensionObject (truncatedSummands K) a.obj ⟶ K.obj (op a) :=
  extensionDesc _ fun A => truncatedSummandInclusion K A.vertex ≫
    truncatedMap K (a := a) (b := A.vertex) A.arrow

private noncomputable def extensionLowIndexEquiv {r : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r)
    (a : SimplexCategory.Truncated r) :
    (extensionObject (truncatedSummands K) a.obj).I ≃ (K.obj (op a)).I :=
  let e : (extensionObject (truncatedSummands K) a.obj).I ≃
      (Σ A : SimplicialObject.Splitting.IndexSet (op a.obj),
        (truncatedComponentIndexExtension K).nonDegenerate A.1.unop.len) :=
    { toFun := fun x => ⟨SimplicialObject.Splitting.IndexSet.mk x.1.down.arrow, x.2⟩
      invFun := fun x =>
        ⟨⟨⟨⟨x.1.1.unop, (SimplexCategory.len_le_of_epi x.1.e).trans a.property⟩,
          x.1.e, inferInstance⟩⟩, x.2⟩
      left_inv := by rintro ⟨⟨⟨⟨b, hb⟩, e, he⟩⟩, x⟩; rfl
      right_inv := by rintro ⟨⟨b, e, he⟩, x⟩; rfl }
  e.trans (truncatedDecompositionIndexEquiv K a.obj.len a.property)

private lemma extensionLowIndexEquiv_apply {r : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r)
    (a : SimplexCategory.Truncated r)
    (x : (extensionObject (truncatedSummands K) a.obj).I) :
    extensionLowIndexEquiv K a x = (extensionLowHom K a).f x := by
  rcases x with ⟨⟨A⟩, x⟩
  show truncatedDecompositionIndexEquiv K a.obj.len a.property
    ⟨SimplicialObject.Splitting.IndexSet.mk A.arrow, x⟩ = _
  rw [truncatedDecompositionIndexEquiv_apply K a.obj.len a.property
    (SimplicialObject.Splitting.IndexSet.mk A.arrow) x]
  apply (truncatedComponentIndexEquiv K a.obj.len a.property).injective
  rw [Equiv.apply_symm_apply]
  let i := (truncatedComponentIndexEquiv K A.vertex.obj.len A.vertex.property).symm x.1
  have hn := truncatedComponentIndexEquiv_naturality K A.vertex.property a.property
    (ObjectProperty.homMk A.arrow : a ⟶ A.vertex).op i
  simp only [i, Equiv.apply_symm_apply] at hn
  exact hn.symm

private noncomputable def truncatedExtensionData {r : ℕ}
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r)
    (h : ∀ {a b : SimplexCategory.Truncated r} (φ : a ⟶ b) [Epi φ]
      (i : (K.obj (op b)).I), IsIso ((K.map φ.op).φ i)) : ExtensionData K where
  N := truncatedSummands K
  ι := truncatedSummandInclusion K
  iso a := by
    have hi : IsIso (extensionLowHom K a) := by
      apply isIso_of_bijective_components
      · have he : (extensionLowHom K a).f = extensionLowIndexEquiv K a :=
          funext fun x => (extensionLowIndexEquiv_apply K a x).symm
        rw [he]
        exact (extensionLowIndexEquiv K a).bijective
      · rintro ⟨⟨A⟩, x⟩
        have : Epi (ObjectProperty.homMk A.arrow : a ⟶ A.vertex) :=
          truncatedHomMkEpi A.arrow
        have hx := h (ObjectProperty.homMk A.arrow : a ⟶ A.vertex)
          ((truncatedComponentIndexEquiv K A.vertex.obj.len A.vertex.property).symm x.1)
        rwa [show (extensionLowHom K a).φ (⟨⟨A⟩, x⟩ :
            (extensionObject (truncatedSummands K) a.obj).I) =
            𝟙 _ ≫ (K.map (ObjectProperty.homMk A.arrow : a ⟶ A.vertex).op).φ
              ((truncatedComponentIndexEquiv K A.vertex.obj.len A.vertex.property).symm x.1)
          from rfl, Category.id_comp]
    exact asIso (extensionLowHom K a)
  fac a A := extensionInclusion_desc _ _ _

private noncomputable def splittingOfIsIsoComponents
    (K : SimplicialObject (FormalCoproduct.{w} C))
    (h : ∀ {m n : SimplexCategory} (φ : m ⟶ n) [Epi φ] (i : (K.obj (op n)).I),
      IsIso ((K.map φ.op).φ i)) : K.Splitting := by
  let N : ℕ → FormalCoproduct.{w} C := nondegSummand K
  let ι : ∀ k, N k ⟶ K.obj (op (SimplexCategory.mk k)) := nondegInclusion K
  refine ⟨N, ι, ?_⟩
  intro Δ
  let F : ULift (SimplicialObject.Splitting.IndexSet Δ) → FormalCoproduct.{w} C :=
    fun A => N A.down.1.unop.len
  let d : Cofan (fun A : SimplicialObject.Splitting.IndexSet Δ => N A.1.unop.len) :=
    Cofan.mk (K.obj Δ) fun A => ι A.1.unop.len ≫ K.map A.e.op
  let d' : Cofan F := Cofan.mk (K.obj Δ) fun A => d.inj A.down
  let c := FormalCoproduct.cofan (ULift (SimplicialObject.Splitting.IndexSet Δ)) F
  let eDown : c.pt.I ≃ Σ A : SimplicialObject.Splitting.IndexSet Δ,
      (componentIndexSSet K).nonDegenerate A.1.unop.len :=
    { toFun := fun p => ⟨p.1.down, p.2⟩
      invFun := fun p => ⟨ULift.up p.1, p.2⟩
      left_inv := by rintro ⟨⟨A⟩, x⟩; rfl
      right_inv := by rintro ⟨A, x⟩; rfl }
  let e := eDown.trans (componentIndexEquiv K Δ)
  let componentIso : ∀ p : c.pt.I, c.pt.obj p ≅ (K.obj Δ).obj (e p) := fun p =>
    isoOfIsIso
      ((K.map (SimplicialObject.Splitting.IndexSet.e p.1.down).op).φ p.2.1)
      (h (SimplicialObject.Splitting.IndexSet.e p.1.down) p.2.1)
  let β : c.pt ≅ K.obj Δ := FormalCoproduct.isoOfComponents e componentIso
  let α : c.pt ⟶ K.obj Δ := β.hom
  let q := FormalCoproduct.coproductIsoCofanPt
    (ULift (SimplicialObject.Splitting.IndexSet Δ)) F
  have hdesc : Sigma.desc d'.inj = q.hom ≫ α := by
    apply colimit.hom_ext
    intro A
    rw [colimit.ι_desc]
    have hcof : colimit.ι (Discrete.functor F) A ≫ q.hom = c.inj A.as := by
      change Sigma.ι F A.as ≫ q.hom = c.inj A.as
      exact FormalCoproduct.ι_comp_coproductIsoCofanPt A.as
    simp only [Cofan.mk_ι_app]
    rw [← Category.assoc, hcof]
    change d.inj A.as.down = c.inj A.as ≫ α
    apply FormalCoproduct.hom_ext rfl
    intro x
    dsimp [d, α, β, c, FormalCoproduct.cofan_inj, FormalCoproduct.isoOfComponents,
      nondegInclusion]
    simp [ι, nondegInclusion]
  letI : IsIso (Sigma.desc d'.inj) := by
    rw [hdesc]
    infer_instance
  have hc' : IsColimit (Cofan.mk (K.obj Δ) fun A : SimplicialObject.Splitting.IndexSet Δ =>
      d'.inj (ULift.up A)) :=
    Cofan.isColimitEquivOfEquiv Equiv.ulift.symm d' (Cofan.isColimitOfIsIsoSigmaDesc d')
  change IsColimit (Cofan.mk (K.obj Δ) fun A : SimplicialObject.Splitting.IndexSet Δ =>
    ι A.1.unop.len ≫ K.map A.e.op)
  simpa [d', d] using hc'

/-- A truncated simplicial object is split when it extends to a split simplicial
object. -/
def IsTruncatedSplit (r : ℕ)
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r) : Prop :=
  ∃ L : SimplicialObject (FormalCoproduct.{w} C),
    Nonempty L.Splitting ∧
      Nonempty (((SimplicialObject.truncation r).obj L) ≅ K)

/-- **Stacks Project, Tag 0DAU, parts (1) and (2).** A simplicial formal
coproduct is split iff each component map over a surjective simplicial
operator is an isomorphism. -/
@[stacks 0DAU "simplicial: (1) iff (2)"]
theorem split_iff_components_of_epi
    (K : SimplicialObject (FormalCoproduct.{w} C)) :
    Nonempty K.Splitting ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n) [Epi φ]
        (i : (K.obj (op n)).I),
        IsIso ((K.map φ.op).φ i) :=
  ⟨fun ⟨s⟩ {m n} φ _ i => isIso_φ_of_comm (splittingDecompositionIso s (op n)).hom
      (splittingDecompositionIso s (op m)).hom (splittingDecompositionIso_naturality s φ)
      (fun _ => inferInstanceAs (IsIso (𝟙 _))) i,
    fun h => ⟨splittingOfIsIsoComponents K h⟩⟩

/-- **Stacks Project, Tag 0DAU, parts (2) and (3).** It suffices to test the
elementary degeneracies of a simplicial formal coproduct. -/
@[stacks 0DAU "simplicial: (2) iff (3)"]
theorem components_of_epi_iff_components_of_degeneracy
    (K : SimplicialObject (FormalCoproduct.{w} C)) :
    (∀ {m n : SimplexCategory} (φ : m ⟶ n) [Epi φ]
      (i : (K.obj (op n)).I), IsIso ((K.map φ.op).φ i)) ↔
    (∀ (n : ℕ) (j : Fin (n + 1))
      (i : (K.obj (op (SimplexCategory.mk n))).I),
      IsIso ((K.map (SimplexCategory.σ j).op).φ i)) := by
  constructor
  · intro h n j i
    exact h (SimplexCategory.σ j) i
  · intro h m n φ hφ i
    cases m using SimplexCategory.rec with
    | mk d =>
      induction d generalizing n i with
      | zero =>
        have hn : n = SimplexCategory.mk 0 :=
          SimplexCategory.ext (Nat.eq_zero_of_le_zero (SimplexCategory.len_le_of_epi φ))
        subst n
        have := isIso_of_epi_of_injective φ fun x y _ => Subsingleton.elim (α := Fin 1) x y
        infer_instance
      | succ d ih =>
        by_cases hinj : Function.Injective φ.toOrderHom
        · have := isIso_of_epi_of_injective φ hinj
          infer_instance
        · obtain ⟨j, ψ, hφ⟩ := SimplexCategory.eq_σ_comp_of_not_injective φ hinj
          have : Epi ψ := epi_of_epi_fac hφ.symm
          rw [hφ]
          exact isIso_φ_map_comp K _ ψ i (ih i ψ) (h d j _)

/-- **Stacks Project, Tag 0DAU, truncated parts (1) and (2).** -/
@[stacks 0DAU "truncated: (1) iff (2)"]
theorem truncated_split_iff_components_of_epi (r : ℕ)
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r) :
    IsTruncatedSplit r K ↔
      ∀ {m n : SimplexCategory.Truncated r} (φ : m ⟶ n) [Epi φ]
        (i : (K.obj (op n)).I),
        IsIso ((K.map φ.op).φ i) := by
  constructor
  · rintro ⟨L, ⟨s⟩, ⟨e⟩⟩ m n φ _ i
    have : Epi φ.hom := SimplexCategory.epi_iff_surjective.2 (truncated_epi_hom_surjective φ)
    exact isIso_φ_of_comm (e.hom.app (op n)) (e.hom.app (op m)) (f := L.map φ.hom.op)
      (e.hom.naturality φ.op).symm ((split_iff_components_of_epi L).mp ⟨s⟩ φ.hom) i
  · intro h
    let d := truncatedExtensionData K h
    refine ⟨extensionFunctor d, ?_, ⟨extensionTruncationIso d⟩⟩
    apply (split_iff_components_of_epi _).mpr
    intro m n e he i
    show IsIso ((extensionMap d e).φ i)
    rw [extensionMap_epi]
    show IsIso (𝟙 _)
    infer_instance

/-- **Stacks Project, Tag 0DAU, truncated parts (2) and (3).** -/
@[stacks 0DAU "truncated: (2) iff (3)"]
theorem truncated_components_of_epi_iff_components_of_degeneracy (r : ℕ)
    (K : SimplicialObject.Truncated (FormalCoproduct.{w} C) r) :
    (∀ {m n : SimplexCategory.Truncated r} (φ : m ⟶ n) [Epi φ]
      (i : (K.obj (op n)).I), IsIso ((K.map φ.op).φ i)) ↔
    (∀ (n : ℕ) (hn : n + 1 ≤ r) (j : Fin (n + 1))
      (i : (K.obj (op (⟨SimplexCategory.mk n, Nat.le_of_succ_le hn⟩ :
        SimplexCategory.Truncated r))).I),
      IsIso ((K.map (ObjectProperty.homMk (SimplexCategory.σ j) :
        (⟨SimplexCategory.mk (n + 1), hn⟩ : SimplexCategory.Truncated r) ⟶
        (⟨SimplexCategory.mk n, Nat.le_of_succ_le hn⟩ :
          SimplexCategory.Truncated r)).op).φ i)) := by
  constructor
  · intro h n hn j i
    have : Epi (ObjectProperty.homMk (SimplexCategory.σ j) :
        (⟨SimplexCategory.mk (n + 1), hn⟩ : SimplexCategory.Truncated r) ⟶
        (⟨SimplexCategory.mk n, Nat.le_of_succ_le hn⟩ :
          SimplexCategory.Truncated r)) := truncatedHomMkEpi _
    exact h _ i
  · intro h m n φ hφ i
    rcases m with ⟨mobj, hm⟩
    cases mobj using SimplexCategory.rec with
    | mk d =>
      exact truncated_epi_components_of_degeneracies K h d hm n φ hφ i

end Stacks.CategoryTheory.Hypercovering

end
