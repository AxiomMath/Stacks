module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GrassmannianConormalEmbedding
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ConstantRank

/-!
# Embedding into a tower of Grassmannian bundles along which every class extends

Let `f : X ⟶ Y` be a closed immersion of smooth projective schemes over `k`, with `X` connected.
For every class `x ∈ K₀(Vect(X))` there is a tower `π : W = Y × G(l₁, n₁) × ⋯ × G(l_s, n_s) ⟶ Y`
of projections, with `0 < l_i < n_i`, and a closed immersion `j : X ⟶ W` with `j ≫ π = f`, such
that `x = j^*y` for some `y ∈ K₀(Vect(W))`.

One adds a Grassmannian for each finite locally free module `ℰ` occurring in `x`, as in the proof
of [Stacks, Tag 0FIR]: on the connected (hence integral) `X` the module `ℰ` has a constant rank
`r`; if `r = 0` then `ℰ = 0`, and otherwise, with `L` ample on the current `W`, a surjection
`𝒪_X^{⊕ m} ⟶ ℰ ⊗ (j^*L)^{⊗ n}` is classified by `g : X ⟶ G(m - r, m)` and
`[ℰ] = g^*[𝒬] · j^*β` (`Stacks.Ample.exists_epi_free_classOf_eq_mul_pullbackRingHom`); the new
embedding is `(j, g) : X ⟶ W × G(m - r, m)`.

This is the geometric part of the proof of [Stacks, Tag 0FIP] given here, which replaces the
splitting principle and Bertini's theorem of the source by Grassmannians.

## Main definitions

* `Stacks.WeilCohomology.SmoothProjectiveScheme.IsGrassmannianTower`: `π` is a composite of
  projections `V × G(l, n) ⟶ V`, `0 < l < n`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.GrassmannianTowerEmbedding`: the data
  `(W, π, j)`.

## Main results

* `Stacks.WeilCohomology.SmoothProjectiveScheme.exists_grassmannianTowerEmbedding`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.VectorBundleKZero

universe u

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k : Type u} [Field k]

/-- **A tower of Grassmannian bundles**: `π : W ⟶ Y` is a composite of projections
`V × G(l, n) ⟶ V` with `0 < l < n`. -/
inductive IsGrassmannianTower : {W Y : (SmoothProjectiveScheme k).FullSubcategory} → (W ⟶ Y) → Prop
  | id (Y : (SmoothProjectiveScheme k).FullSubcategory) : IsGrassmannianTower (𝟙 Y)
  | comp {V Y : (SmoothProjectiveScheme k).FullSubcategory} (π : V ⟶ Y) (l n : ℕ) (hl : 0 < l)
      (hln : l < n) :
      IsGrassmannianTower π →
        IsGrassmannianTower (fst V (SmoothProjectiveScheme.grassmannian k l n) ≫ π)

/-- **An embedding of `X` into a Grassmannian tower over `Y` lifting `f : X ⟶ Y`**: a tower
`π : W ⟶ Y` and a closed immersion `j : X ⟶ W` with `j ≫ π = f`. -/
structure GrassmannianTowerEmbedding {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) where
  /-- The top of the tower. -/
  W : (SmoothProjectiveScheme k).FullSubcategory
  /-- The tower. -/
  π : W ⟶ Y
  /-- The embedding. -/
  j : X ⟶ W
  isClosedImmersion : IsClosedImmersion j.hom.left
  fac : j ≫ π = f
  isTower : IsGrassmannianTower π

namespace GrassmannianTowerEmbedding

variable {X Y : (SmoothProjectiveScheme k).FullSubcategory} {f : X ⟶ Y}

/-- The classes of `K₀(Vect(X))` that extend to the top of the tower. -/
def Extends (T : GrassmannianTowerEmbedding f) (x : VectorBundleKZero X.obj.left) : Prop :=
  ∃ y : VectorBundleKZero T.W.obj.left, pullbackRingHom T.j.hom.left y = x

/-- `T'` refines `T`: its embedding lifts that of `T`. -/
def Refines (T' T : GrassmannianTowerEmbedding f) : Prop :=
  ∃ ρ : T'.W ⟶ T.W, T'.j ≫ ρ = T.j

/-- Every tower embedding refines itself. -/
theorem Refines.refl (T : GrassmannianTowerEmbedding f) : T.Refines T :=
  ⟨𝟙 _, Category.comp_id _⟩

/-- Refinement of tower embeddings is transitive. -/
theorem Refines.trans {T'' T' T : GrassmannianTowerEmbedding f} (h₁ : T''.Refines T')
    (h₂ : T'.Refines T) : T''.Refines T := by
  obtain ⟨ρ₁, h₁⟩ := h₁
  obtain ⟨ρ₂, h₂⟩ := h₂
  exact ⟨ρ₁ ≫ ρ₂, by rw [← Category.assoc, h₁, h₂]⟩

/-- A class extending to `T` extends to every refinement of `T`. -/
theorem Extends.of_refines {T' T : GrassmannianTowerEmbedding f} (h : T'.Refines T)
    {x : VectorBundleKZero X.obj.left} (hx : T.Extends x) : T'.Extends x := by
  obtain ⟨ρ, hρ⟩ := h
  obtain ⟨y, rfl⟩ := hx
  refine ⟨pullbackRingHom ρ.hom.left y, ?_⟩
  rw [← pullbackRingHom_comp_apply]
  congr 2
  rw [← Over.comp_left, ← ObjectProperty.FullSubcategory.comp_hom, hρ]

/-- The class `0` extends to the top of the tower. -/
theorem extends_zero (T : GrassmannianTowerEmbedding f) : T.Extends 0 :=
  ⟨0, map_zero _⟩

/-- A sum of classes extending to the top of the tower extends to it. -/
theorem Extends.add {T : GrassmannianTowerEmbedding f} {x x' : VectorBundleKZero X.obj.left}
    (hx : T.Extends x) (hx' : T.Extends x') : T.Extends (x + x') := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨y', rfl⟩ := hx'
  exact ⟨y + y', map_add _ _ _⟩

/-- The negative of a class extending to the top of the tower extends to it. -/
theorem Extends.neg {T : GrassmannianTowerEmbedding f} {x : VectorBundleKZero X.obj.left}
    (hx : T.Extends x) : T.Extends (-x) := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨-y, map_neg _ _⟩

/-- **The extension step.** Given a tower embedding `T` and a finite locally free `ℰ` of
constant rank `r > 0` on `X`, the embedding `(j, g) : X ⟶ W × G(m - r, m)` refines `T` and the
class of `ℰ` extends to it. -/
theorem exists_refines_extends_of_rank (T : GrassmannianTowerEmbedding f) (E : X.obj.left.Modules)
    (r : ℕ) (hr : 0 < r)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    ∃ T' : GrassmannianTowerEmbedding f, T'.Refines T ∧ T'.Extends (classOf X.obj.left E) := by
  have := T.isClosedImmersion
  obtain ⟨L, hLinv, -, hL⟩ :=
    Stacks.Algebraization.exists_isRelativelyAmple_of_isProjective k T.W.obj.hom
      (SmoothProjectiveScheme.isProjective T.W)
  have := hLinv
  obtain ⟨m, hm, Q, φ, hφ, hQ, β, hβ⟩ :=
    Stacks.Ample.exists_epi_free_classOf_eq_mul_pullbackRingHom L T.j.hom.left hL E r (r + 1)
  have hQ' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Q
      (m - (m - r)) := by
    rwa [Nat.sub_sub_self (by omega : r ≤ m)]
  have := hφ
  have := hQ'
  obtain ⟨g, hg⟩ := Grassmannian.exists_pullbackRingHom_universalClass_eq_classOf
    (k := m - r) Q φ
  set G := SmoothProjectiveScheme.grassmannian k (m - r) m
  let g' : X.obj.left ⟶ G.obj.left :=
    pullback.lift (f := terminal.from (Spec (.of k)))
      (g := terminal.from (Grassmannian.scheme.{u} (m - r) m)) X.obj.hom g
      (terminal.hom_ext _ _)
  have hg'G : g' ≫ G.obj.hom = X.obj.hom := pullback.lift_fst _ _ _
  let τ : G.obj.left ⟶ Grassmannian.scheme.{u} (m - r) m :=
    pullback.snd (terminal.from (Spec (.of k)))
      (terminal.from (Grassmannian.scheme.{u} (m - r) m))
  have hg'q : g' ≫ τ = g := pullback.lift_snd _ _ _
  let hl : X.obj.left ⟶ Limits.pullback T.W.obj.hom G.obj.hom :=
    pullback.lift T.j.hom.left g' (by rw [Over.w T.j.hom, hg'G])
  have hlfst : hl ≫ pullback.fst T.W.obj.hom G.obj.hom = T.j.hom.left := pullback.lift_fst _ _ _
  have hlsnd : hl ≫ pullback.snd T.W.obj.hom G.obj.hom = g' := pullback.lift_snd _ _ _
  let h : X ⟶ prod T.W G := ObjectProperty.homMk (Over.homMk hl (by
    show hl ≫ pullback.fst T.W.obj.hom G.obj.hom ≫ T.W.obj.hom = X.obj.hom
    rw [← Category.assoc, hlfst, Over.w T.j.hom]))
  have : IsClosedImmersion (hl ≫ pullback.fst T.W.obj.hom G.obj.hom) := by rwa [hlfst]
  have : IsClosedImmersion hl := .of_comp hl (pullback.fst _ _)
  have hhfst : h ≫ fst T.W G = T.j := ObjectProperty.hom_ext _ (Over.OverMorphism.ext hlfst)
  refine ⟨⟨prod T.W G, fst T.W G ≫ T.π, h, ‹_›, ?_,
    IsGrassmannianTower.comp T.π (m - r) m (by omega) (by omega) T.isTower⟩,
    ⟨fst T.W G, hhfst⟩, ?_⟩
  · rw [← Category.assoc, hhfst, T.fac]
  refine ⟨pullbackRingHom (pullback.snd T.W.obj.hom G.obj.hom ≫ τ)
      (Grassmannian.universalClass.{u} (m - r) m) *
    pullbackRingHom (pullback.fst T.W.obj.hom G.obj.hom) β, ?_⟩
  show pullbackRingHom hl _ = _
  rw [map_mul, ← pullbackRingHom_comp_apply, ← pullbackRingHom_comp_apply, ← Category.assoc,
    hlsnd, hg'q, hlfst, hg, hβ]

/-- **Every class extends to some refinement**, for `X` connected. -/
theorem exists_refines_extends [ConnectedSpace X.obj.left] (T : GrassmannianTowerEmbedding f)
    (x : VectorBundleKZero X.obj.left) :
    ∃ T' : GrassmannianTowerEmbedding f, T'.Refines T ∧ T'.Extends x := by
  have : IsIntegral X.obj.left :=
    Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (k := k) X.obj.hom
  obtain ⟨p, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
  induction p using FreeAbelianGroup.induction_on generalizing T with
  | zero => exact ⟨T, Refines.refl T, by simpa using T.extends_zero⟩
  | of M =>
    by_cases hM : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u}
        (R := X.obj.left.ringCatSheaf) M
    · have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
          (R := X.obj.left.ringCatSheaf) M := ⟨hM.exists_isFiniteLocallyFreeData⟩
      obtain ⟨x₀⟩ : Nonempty X.obj.left := inferInstance
      obtain ⟨r, hr⟩ : ∃ r : ℕ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          M r := ⟨_, Scheme.Modules.isFiniteLocallyFreeOfRank_of_fiberRank_eq M _ x₀ rfl⟩
      rcases Nat.eq_zero_or_pos r with rfl | hr0
      · exact ⟨T, .refl T, 0, (map_zero _).trans (VectorBundleKZero.classOf_eq_zero_of_isZero
          (@Stacks.Chow.isZero_of_isFiniteLocallyFreeOfRank_zero _ _ hr)).symm⟩
      · exact exists_refines_extends_of_rank T M r hr0
    · exact ⟨T, .refl T, 0, (map_zero _).trans
        (VectorBundleKZero.classOf_eq_zero_of_not_isFiniteLocallyFree M hM).symm⟩
  | neg p hp =>
    obtain ⟨T', hT', hx⟩ := hp T
    exact ⟨T', hT', by simpa only [map_neg] using hx.neg⟩
  | add p p' hp hp' =>
    obtain ⟨T₁, hT₁, hx₁⟩ := hp T
    obtain ⟨T₂, hT₂, hx₂⟩ := hp' T₁
    exact ⟨T₂, hT₂.trans hT₁, by simpa only [map_add] using (hx₁.of_refines hT₂).add hx₂⟩

end GrassmannianTowerEmbedding

/-- The trivial tower embedding of a closed immersion. -/
def GrassmannianTowerEmbedding.ofClosedImmersion {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) [IsClosedImmersion f.hom.left] : GrassmannianTowerEmbedding f :=
  ⟨Y, 𝟙 Y, f, inferInstance, Category.comp_id f, IsGrassmannianTower.id Y⟩

/-- **The embedding of the proof of Stacks 0FIP.** For a closed immersion `f : X ⟶ Y` of smooth
projective schemes over `k` with `X` connected and any `x ∈ K₀(Vect(X))` there are a tower of
Grassmannian bundles `π : W ⟶ Y` and a closed immersion `j : X ⟶ W` with `j ≫ π = f` and
`x = j^*y` for some `y ∈ K₀(Vect(W))`. -/
theorem exists_grassmannianTowerEmbedding {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) [IsClosedImmersion f.hom.left] [ConnectedSpace X.obj.left]
    (x : VectorBundleKZero X.obj.left) :
    ∃ T : GrassmannianTowerEmbedding f, T.Extends x :=
  ((GrassmannianTowerEmbedding.ofClosedImmersion f).exists_refines_extends x).imp fun _ h => h.2

end Stacks.WeilCohomology.SmoothProjectiveScheme

end
