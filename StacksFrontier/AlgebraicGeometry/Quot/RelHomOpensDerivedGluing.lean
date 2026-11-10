module

public import StacksFrontier.AlgebraicGeometry.Quot.RelHomOpensCochains
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveCocycleClasses

/-!
# Gluing morphisms of derived inverse images over the opens of a space

Let `P` be a coherent pullback pseudofunctor datum of additive functors between abelian
categories `M a`, `E` left derived functors of the induced datum on homotopy categories with
values in the derived categories (the localization functors being `DerivedCategory.Qh`), and `κ`
a cone over `a₀` from a functor `π : Opens X₀ ⥤ A`.  Let `K`, `L` be complexes of `M a₀`, the
terms of `L` injective, such that

* the relative Hom presheaves `W ↦ Hom((κ W)^*N, (κ W)^*N')` are sheaves, flasque when `N'` is
  injective;
* `(κ W)^*L` is K-injective for every `W`, and the comparisons `α` of the derived inverse images
  with the underived ones are invertible along the legs;
* `Ext^{-1}((κ W)^*K, (κ W)^*L) = 0` in the derived category for every open `W`.

Then `W ↦ Hom_D((κ W)^*K, (κ W)^*L)` is a sheaf on the opens of `X₀`
(`CategoryTheory.PullbackData.existsUnique_relHomMap_glue`).  This is the form of Stacks 0D66
used for the Zariski gluing of `T ↦ Hom(K_T, E_T)`: by the comparisons `α`, a morphism over `W` is
the class of a degree `0` cocycle of `Hom^•((κ W)^*K, (κ W)^*L)`
(`CategoryTheory.PullbackData.cocycleClass`), naturally in `W`
(`CategoryTheory.PullbackData.relHomMap_cocycleClass`), two cocycles have the same class exactly
when they differ by a coboundary, and the vanishing of `Ext⁻¹` is exactness in degree `-1`; so
the gluing is `Stacks.FlasqueCokernel.FlasqueTriple.exists_glue_mod_boundary`.

Nothing here is registered.

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace CochainComplex.HomComplex
open Stacks.FlasqueCokernel DerivedCategory

universe w v₀ v₁ u₁ v₂ u₂

namespace CategoryTheory.PullbackData

variable {X₀ : Type v₀} [TopologicalSpace X₀]
  {A : Type u₁} [Category.{v₁} A] {M : A → Type u₂} [∀ a, Category.{v₂} (M a)]
  [∀ a, Abelian (M a)] [∀ a, HasDerivedCategory.{w} (M a)] (P : PullbackData A M)
  [hadd : ∀ {a b : A} (f : a ⟶ b), (P.pull f).Additive] (hP : P.IsCoherent)
  (E : P.mapHomotopyCategory.LeftDerived (fun a => DerivedCategory (M a)))
  {π : Opens X₀ ⥤ A} {a₀ : A} (κ : ConeTo π a₀) (K L : CochainComplex (M a₀) ℤ)

/-- Conjugation by two isomorphisms, solved for the conjugated morphism. -/
theorem _root_.CategoryTheory.Iso.hom_comp_comp_inv_eq_of_eq {C : Type*} [Category* C]
    {X Y X' Y' : C} (a : X ≅ X') (b : Y ≅ Y') {ψ : X' ⟶ Y'} {φ : X ⟶ Y}
    (h : ψ = a.inv ≫ φ ≫ b.hom) : a.hom ≫ ψ ≫ b.inv = φ := by
  rw [h]
  simp

/-- **The naturality square of the class of a cocycle, with every object and morphism a
variable.**  `T`, `T'` are the comparison triangles of the derived inverse images, `aW`, `aV` the
comparisons `α` along the two legs, `αK`, `αL` the comparison along the transition morphism and
`τK`, `τL` the underived triangles. -/
theorem conj_eq_of_comparisons {C₁ C₂ : Type*} [Category* C₁] [Category* C₂] (Lf : C₁ ⥤ C₂)
    {LK LY QK QL : C₁} {VX VY QK' QL' FK FL : C₂} (T : VX ≅ Lf.obj LK) (T' : VY ≅ Lf.obj LY)
    (aWK : LK ≅ QK) (aWL : LY ≅ QL) (aVK : VX ≅ QK') (aVL : VY ≅ QL') (u : QK ⟶ QL)
    (u' : QK' ⟶ QL') (αK : Lf.obj QK ⟶ FK) (αL : Lf.obj QL ⟶ FL) (τK : FK ⟶ QK') (τL : FL ⟶ QL')
    (Fu : FK ⟶ FL) (tK : T.inv ≫ aVK.hom = Lf.map aWK.hom ≫ αK ≫ τK)
    (tL : T'.inv ≫ aVL.hom = Lf.map aWL.hom ≫ αL ≫ τL) (nα : Lf.map u ≫ αL = αK ≫ Fu)
    (key : Fu ≫ τL = τK ≫ u') :
    T.hom ≫ Lf.map (aWK.hom ≫ u ≫ aWL.inv) ≫ T'.inv = aVK.hom ≫ u' ≫ aVL.inv := by
  rw [← cancel_epi T.inv, Iso.inv_hom_id_assoc, ← cancel_mono aVL.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [tL, reassoc_of% tK, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  rw [← Lf.map_comp_assoc aWL.inv, Iso.inv_hom_id, Lf.map_id, Category.id_comp, reassoc_of% nα,
    key]

/-- The comparison `α` along the leg at an open, as an isomorphism. -/
def legαIso (hα : ∀ W N, IsIso ((E.α (κ.leg W)).app N)) (W : Opens X₀)
    (N : HomotopyCategory (M a₀) (ComplexShape.up ℤ)) :
    (E.L (κ.leg W)).obj ((E.Q a₀).obj N) ≅
      (E.Q (π.obj W)).obj ((P.mapHomotopyCategory.pull (κ.leg W)).obj N) :=
  @asIso _ _ _ _ ((E.α (κ.leg W)).app N) (hα W N)

/-- **The morphism of derived inverse images attached to a degree `0` cocycle** over an open
`W`: its class in the derived category, read through the comparisons `α` along the leg. -/
def cocycleClass (hα : ∀ W N, IsIso ((E.α (κ.leg W)).app N)) (W : Opens X₀)
    (z : Cocycle (P.legComplex κ K W) (P.legComplex κ L W) 0) :
    E.toPullbackData.relHomObj κ
      ((E.Q a₀).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
      ((E.Q a₀).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) W :=
  (P.legαIso E κ hα W ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)).hom ≫
    (E.Q (π.obj W)).map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (Cocycle.homOf z)) ≫
    (P.legαIso E κ hα W ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)).inv

omit [∀ a, HasDerivedCategory.{w} (M a)] in
/-- The degreewise identity behind the naturality of `cocycleClass`. -/
theorem triangle_inv_comp_homOf_cochainRes {V W : Opens X₀} (h : V ≤ W)
    (z : Cocycle (P.legComplex κ K W) (P.legComplex κ L W) 0) :
    (NatTrans.mapHomologicalComplex (P.triangle (κ.w (homOfLE h))).inv (ComplexShape.up ℤ)).app
        K ≫ Cocycle.homOf ((P.cocycleOpens hP κ K L).res h z) =
      ((P.pull (π.map (homOfLE h))).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (Cocycle.homOf z) ≫
        (NatTrans.mapHomologicalComplex (P.triangle (κ.w (homOfLE h))).inv
          (ComplexShape.up ℤ)).app L := by
  ext p
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, Cocycle.homOf_f]
  change _ ≫ P.relHomMap κ (K.X p) (L.X p) (homOfLE h)
    ((z : Cochain (P.legComplex κ K W) (P.legComplex κ L W) 0).v p p (add_zero p)) = _
  simp only [relHomMap, Functor.conjHom, Iso.inv_hom_id_app_assoc]

/-- **The class of a cocycle is natural in the open.** -/
theorem relHomMap_cocycleClass (hα : ∀ W N, IsIso ((E.α (κ.leg W)).app N))
    {V W : Opens X₀} (h : V ≤ W) (z : Cocycle (P.legComplex κ K W) (P.legComplex κ L W) 0) :
    E.toPullbackData.relHomMap κ _ _ (homOfLE h) (P.cocycleClass E κ K L hα W z) =
      P.cocycleClass E κ K L hα V ((P.cocycleOpens hP κ K L).res h z) := by
  have hk : π.map (homOfLE h) ≫ κ.leg W = κ.leg V := κ.w (homOfLE h)
  have tK := E.triangle_inv_app_comp_α hk
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)
  have tL := E.triangle_inv_app_comp_α hk
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)
  rw [mapHomotopyCategory_triangle_inv_app] at tK tL
  have nα := (E.α (π.map (homOfLE h))).naturality
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (Cocycle.homOf z))
  simp only [Functor.comp_map] at nα
  have key := congrArg
    (fun t => (E.Q (π.obj V)).map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map t))
    (P.triangle_inv_comp_homOf_cochainRes hP κ K L h z).symm
  simp only [Functor.map_comp] at key
  exact conj_eq_of_comparisons (E.L (π.map (homOfLE h)))
    ((E.toPullbackData.triangle hk).app _) ((E.toPullbackData.triangle hk).app _)
    (P.legαIso E κ hα W ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    (P.legαIso E κ hα W ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L))
    (P.legαIso E κ hα V ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    (P.legαIso E κ hα V ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L))
    _ _ _ _ _ _ _ tK tL nα key

/-- **Every morphism of derived inverse images is the class of a cocycle.** -/
theorem cocycleClass_surjective (hQ : ∀ a, E.Q a = DerivedCategory.Qh)
    (hα : ∀ W N, IsIso ((E.α (κ.leg W)).app N)) (W : Opens X₀)
    [(P.legComplex κ L W).IsKInjective] :
    Function.Surjective (P.cocycleClass E κ K L hα W) := by
  intro φ
  have hs : ∀ ψ : (E.Q (π.obj W)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (P.legComplex κ K W)) ⟶
      (E.Q (π.obj W)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (P.legComplex κ L W)),
      ∃ u : P.legComplex κ K W ⟶ P.legComplex κ L W,
        (E.Q (π.obj W)).map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map u) = ψ := by
    rw [hQ]
    exact fun ψ => CochainComplex.IsKInjective.Qh_map_quotient_map_surjective ψ
  obtain ⟨u, hu⟩ :=
    hs ((P.legαIso E κ hα W ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)).inv ≫ φ ≫
      (P.legαIso E κ hα W ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)).hom)
  refine ⟨Cocycle.ofHom u, ?_⟩
  have e1 : P.cocycleClass E κ K L hα W (Cocycle.ofHom u) =
      (P.legαIso E κ hα W ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)).hom ≫
        (E.Q (π.obj W)).map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map u) ≫
        (P.legαIso E κ hα W ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)).inv :=
    congrArg (fun v =>
      (P.legαIso E κ hα W ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)).hom ≫
        (E.Q (π.obj W)).map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map v) ≫
        (P.legαIso E κ hα W ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)).inv)
      (Cocycle.homOf_ofHom_eq_self u)
  exact e1.trans (Iso.hom_comp_comp_inv_eq_of_eq _ _ hu)

/-- **Two cocycles have the same class exactly when they differ by a coboundary.** -/
theorem cocycleClass_eq_iff (hQ : ∀ a, E.Q a = DerivedCategory.Qh)
    (hα : ∀ W N, IsIso ((E.α (κ.leg W)).app N)) (W : Opens X₀)
    [(P.legComplex κ L W).IsKInjective]
    (z z' : Cocycle (P.legComplex κ K W) (P.legComplex κ L W) 0) :
    P.cocycleClass E κ K L hα W z = P.cocycleClass E κ K L hα W z' ↔
      ∃ c : Cochain (P.legComplex κ K W) (P.legComplex κ L W) (-1),
        δ (-1) 0 c = z.1 - z'.1 := by
  have hk : (E.Q (π.obj W)).map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (Cocycle.homOf z)) =
      (E.Q (π.obj W)).map
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map (Cocycle.homOf z')) ↔
      ∃ c : Cochain (P.legComplex κ K W) (P.legComplex κ L W) (-1),
        δ (-1) 0 c = z.1 - z'.1 := by
    rw [hQ]
    exact CochainComplex.IsKInjective.Qh_map_quotient_map_homOf_eq_iff z z'
  rw [cocycleClass, cocycleClass]
  exact (Iso.cancel_iso_hom_left _ _ _).trans ((Iso.cancel_iso_inv_right _ _ _).trans hk)

/-- **The vanishing of `Ext⁻¹` is exactness in degree `-1`.** -/
theorem exists_δ_eq_of_ext_neg_one (hQ : ∀ a, E.Q a = DerivedCategory.Qh)
    (hα : ∀ W N, IsIso ((E.α (κ.leg W)).app N)) (W : Opens X₀)
    [(P.legComplex κ L W).IsKInjective]
    (hneg : Subsingleton
      ((E.L (κ.leg W)).obj
          ((E.Q a₀).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ⟶
        ((E.L (κ.leg W)).obj
          ((E.Q a₀).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)))⟦(-1 : ℤ)⟧))
    (z : Cochain (P.legComplex κ K W) (P.legComplex κ L W) (-1)) (hz : δ (-1) 0 z = 0) :
    ∃ e, δ (-2) (-1) e = z := by
  have hsub : Subsingleton ((E.Q (π.obj W)).obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (P.legComplex κ K W)) ⟶
        ((E.Q (π.obj W)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (P.legComplex κ L W)))⟦(-1 : ℤ)⟧) :=
    ⟨fun a b => by
      have := hneg.elim
        ((P.legαIso E κ hα W ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)).hom ≫ a ≫
          ((shiftFunctor _ (-1 : ℤ)).mapIso
            (P.legαIso E κ hα W ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L))).inv)
        ((P.legαIso E κ hα W ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)).hom ≫ b ≫
          ((shiftFunctor _ (-1 : ℤ)).mapIso
            (P.legαIso E κ hα W ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L))).inv)
      exact (Iso.cancel_iso_inv_right _ _ _).1 ((Iso.cancel_iso_hom_left _ _ _).1 this)⟩
  have hex : Subsingleton ((E.Q (π.obj W)).obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (P.legComplex κ K W)) ⟶
        ((E.Q (π.obj W)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (P.legComplex κ L W)))⟦(-1 : ℤ)⟧) →
      ∃ e : Cochain (P.legComplex κ K W) (P.legComplex κ L W) (-2), δ (-2) (-1) e = z := by
    rw [hQ]
    exact fun h => CochainComplex.IsKInjective.exists_δ_eq_of_subsingleton h z hz
  exact hex hsub

/-- **Gluing of morphisms of derived inverse images over the opens of `X₀`** (Stacks 0D66 in the
flasque form): under the hypotheses of the module documentation, morphisms
`(κ V i)^*K ⟶ (κ V i)^*L` of the derived categories over the members of an open covering of `U`
which agree on the overlaps come from exactly one morphism over `U`. -/
theorem existsUnique_relHomMap_glue (hQ : ∀ a, E.Q a = DerivedCategory.Qh)
    (hsh : ∀ N N' : M a₀, (P.relHomOpens hP κ N N').IsSheaf)
    (hfl : ∀ N N' : M a₀, Injective N' → (P.relHomOpens hP κ N N').IsFlasque)
    (hL : ∀ p, Injective (L.X p)) (hKi : ∀ W, (P.legComplex κ L W).IsKInjective)
    (hα : ∀ W N, IsIso ((E.α (κ.leg W)).app N))
    (hneg : ∀ W, Subsingleton
      ((E.L (κ.leg W)).obj
          ((E.Q a₀).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) ⟶
        ((E.L (κ.leg W)).obj
          ((E.Q a₀).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)))⟦(-1 : ℤ)⟧))
    {U : Opens X₀} {ι : Type*} (V : ι → Opens X₀) (hV : ∀ i, V i ≤ U) (hsup : iSup V = U)
    (x : ∀ i, E.toPullbackData.relHomObj κ
      ((E.Q a₀).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
      ((E.Q a₀).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) (V i))
    (hx : ∀ i k, E.toPullbackData.relHomMap κ _ _ (homOfLE (inf_le_left : V i ⊓ V k ≤ V i))
        (x i) = E.toPullbackData.relHomMap κ _ _ (homOfLE inf_le_right) (x k)) :
    ∃! y : E.toPullbackData.relHomObj κ
        ((E.Q a₀).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
        ((E.Q a₀).obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)) U,
      ∀ i, E.toPullbackData.relHomMap κ _ _ (homOfLE (hV i)) y = x i := by
  have hex : ∀ (W : Opens X₀) (z : Cochain (P.legComplex κ K W) (P.legComplex κ L W) (-1)),
      δ (-1) 0 z = 0 → ∃ e, δ (-2) (-1) e = z := fun W z hz =>
    have := hKi W
    P.exists_δ_eq_of_ext_neg_one E κ K L hQ hα W (hneg W) z hz
  have hbd : ∀ W (z z' : Cocycle (P.legComplex κ K W) (P.legComplex κ L W) 0),
      P.cocycleClass E κ K L hα W z = P.cocycleClass E κ K L hα W z' ↔
        ∃ c : Cochain (P.legComplex κ K W) (P.legComplex κ L W) (-1), δ (-1) 0 c = z.1 - z'.1 :=
    fun W z z' =>
      have := hKi W
      P.cocycleClass_eq_iff E κ K L hQ hα W z z'
  have hsurj : ∀ W, Function.Surjective (P.cocycleClass E κ K L hα W) := fun W =>
    have := hKi W
    P.cocycleClass_surjective E κ K L hQ hα W
  have hnat := fun {V W : Opens X₀} (h : V ≤ W) z =>
    P.relHomMap_cocycleClass hP E κ K L hα h z
  choose z hz using fun i => hsurj (V i) (x i)
  have hcomp : ∀ i k, (P.cochainFlasqueTriple hP κ K L hsh hfl hL hex).IsBoundary (V i ⊓ V k)
      ((P.cocycleOpens hP κ K L).res inf_le_left (z i) -
        (P.cocycleOpens hP κ K L).res inf_le_right (z k)) := by
    intro i k
    obtain ⟨c, hc⟩ := (hbd _ _ _).1
      (((hnat _ (z i)).symm.trans (by rw [hz, hz]; exact hx i k)).trans (hnat _ (z k)))
    exact ⟨c, Cocycle.ext hc⟩
  obtain ⟨⟨y, hy⟩, hyu⟩ :=
    (P.cochainFlasqueTriple hP κ K L hsh hfl hL hex).exists_glue_mod_boundary V hV hsup z hcomp
  have hres : ∀ y' : Cocycle (P.legComplex κ K U) (P.legComplex κ L U) 0,
      (∀ i, E.toPullbackData.relHomMap κ _ _ (homOfLE (hV i))
        (P.cocycleClass E κ K L hα U y') = x i) ↔
      ∀ i, (P.cochainFlasqueTriple hP κ K L hsh hfl hL hex).IsBoundary (V i)
        ((P.cocycleOpens hP κ K L).res (hV i) y' -
          (show (P.cocycleOpens hP κ K L).obj (V i) from z i)) := by
    intro y'
    refine forall_congr' fun i => ?_
    rw [hnat, ← hz i]
    exact (hbd _ _ _).trans
      ⟨fun ⟨c, hc⟩ => ⟨c, Cocycle.ext hc⟩, fun ⟨c, hc⟩ => ⟨c, congrArg Subtype.val hc⟩⟩
  refine ⟨P.cocycleClass E κ K L hα U y, (hres y).2 hy, fun y₁ hy₁ => ?_⟩
  obtain ⟨y', rfl⟩ := hsurj U y₁
  obtain ⟨c, hc⟩ := hyu y' y ((hres y').1 hy₁) hy
  exact (hbd U y' y).2 ⟨c, congrArg Subtype.val hc⟩

end CategoryTheory.PullbackData

end
