module

public import StacksFrontier.AlgebraicGeometry.Simplicial.GroupoidNerveDescent
public import StacksFrontier.AlgebraicGeometry.Simplicial.DescentViaSimplicialSchemes
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.DescentData
public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime

/-!
# Chosen fibre products of `(X/S)_•` and the cocycle condition of descent data

Let `f : X ⟶ S` be a morphism of schemes and `(X/S)_•` the simplicial scheme of Stacks 024A.
Its degree-one part, with the two vertex projections, is a chosen fibre product `X ×_S X`, and
its degree-two part, with the faces `δ²₂`, `δ²₀`, `δ²₁`, is a chosen triple fibre product
(`AlgebraicGeometry.SimplicialScheme.cechChosenPullback` and `cechChosenPullback₃`). This file
compares the two forms of the cocycle condition that meet there: the cocycle condition of a pair
`(F, α)` on `(X/S)_•` (Stacks 07TH), and the cocycle condition of a descent datum relative to `{f}`
presented over chosen fibre products (`CategoryTheory.Pseudofunctor.DescentData'`).

## Main definitions

* `AlgebraicGeometry.SimplicialScheme.cechChosenPullback`: `(X/S)_1` as a chosen fibre product of
  `f` with itself.
* `AlgebraicGeometry.SimplicialScheme.cechChosenPullback₃`: `(X/S)_2` as a chosen triple fibre
  product of `f`.
* `AlgebraicGeometry.SimplicialScheme.descentData'OfPUnit`: a descent datum over chosen fibre
  products for a one-member family, from an isomorphism satisfying the cocycle condition.

## Main results

* `AlgebraicGeometry.SimplicialScheme.isCocycle_cechTransport_iff_reindexCocycle`: the cocycle
  condition of the pair transported from `γ : pr_0^* M ⟶ pr_1^* M` is the reindexed cocycle
  condition of `γ` along the faces of `(X/S)_2`.
* `AlgebraicGeometry.SimplicialScheme.pullHom_comp_iff_reindexCocycle`: the cocycle condition of
  a descent morphism of sheaves of modules, written with `pullHom`, is the reindexed cocycle
  condition.
* `AlgebraicGeometry.SimplicialScheme.pullHom'_hom_self_of_comp`: the normalization of a descent
  datum along the diagonal follows from the cocycle condition and invertibility.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace AlgebraicGeometry.SimplicialScheme

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The degree-one face maps of `(X/S)_•` read on vertices. -/
@[reassoc]
lemma map_delta_proj_two (i : Fin 3) (k : Fin 2) :
    (simplicialScheme f).map (SimplexCategory.δ i).op ≫ proj f 1 k =
      proj f 2 ((SimplexCategory.δ i).toOrderHom k) :=
  map_proj f (SimplexCategory.δ i) k

/-- The degree-one part of `(X/S)_•` is a chosen fibre product of `f` with itself, with the two
vertex projections. -/
abbrev cechChosenPullback : ChosenPullback f f where
  pullback := (simplicialScheme f).obj (op ⦋1⦌)
  p₁ := proj f 1 0
  p₂ := proj f 1 1
  condition := by simp
  isLimit := PullbackCone.IsLimit.mk _ (fun s => edgeSimplex f s.fst s.snd s.condition)
    (fun s => by simp) (fun s => by simp)
    (fun s m h₁ h₂ => one_hom_ext f (by simpa using h₁) (by simpa using h₂))
  p := baseMap f 1
  hp₁ := by simp

/-- The first projection of `cechChosenPullback f` is the vertex projection `proj f 1 0`. -/
@[simp] lemma cechChosenPullback_p₁ : (cechChosenPullback f).p₁ = proj f 1 0 := rfl
/-- The second projection of `cechChosenPullback f` is the vertex projection `proj f 1 1`. -/
@[simp] lemma cechChosenPullback_p₂ : (cechChosenPullback f).p₂ = proj f 1 1 := rfl
/-- The structure map of `cechChosenPullback f` to `S` is `baseMap f 1`. -/
@[simp] lemma cechChosenPullback_p : (cechChosenPullback f).p = baseMap f 1 := rfl

/-- The face `δ²₂` followed by the vertex projection `proj f 1 0` is `proj f 2 0`. -/
lemma cech_delta_two_proj_zero : (simplicialScheme f).map (SimplexCategory.δ (2 : Fin 3)).op ≫
    proj f 1 0 = proj f 2 0 := by rw [map_delta_proj_two]; rfl
/-- The face `δ²₂` followed by the vertex projection `proj f 1 1` is `proj f 2 1`. -/
lemma cech_delta_two_proj_one : (simplicialScheme f).map (SimplexCategory.δ (2 : Fin 3)).op ≫
    proj f 1 1 = proj f 2 1 := by rw [map_delta_proj_two]; rfl
/-- The face `δ²₁` followed by the vertex projection `proj f 1 0` is `proj f 2 0`. -/
lemma cech_delta_one_proj_zero : (simplicialScheme f).map (SimplexCategory.δ (1 : Fin 3)).op ≫
    proj f 1 0 = proj f 2 0 := by rw [map_delta_proj_two]; rfl
/-- The face `δ²₁` followed by the vertex projection `proj f 1 1` is `proj f 2 2`. -/
lemma cech_delta_one_proj_one : (simplicialScheme f).map (SimplexCategory.δ (1 : Fin 3)).op ≫
    proj f 1 1 = proj f 2 2 := by rw [map_delta_proj_two]; rfl
/-- The face `δ²₀` followed by the vertex projection `proj f 1 0` is `proj f 2 1`. -/
lemma cech_delta_zero_proj_zero : (simplicialScheme f).map (SimplexCategory.δ (0 : Fin 3)).op ≫
    proj f 1 0 = proj f 2 1 := by rw [map_delta_proj_two]; rfl
/-- The face `δ²₀` followed by the vertex projection `proj f 1 1` is `proj f 2 2`. -/
lemma cech_delta_zero_proj_one : (simplicialScheme f).map (SimplexCategory.δ (0 : Fin 3)).op ≫
    proj f 1 1 = proj f 2 2 := by rw [map_delta_proj_two]; rfl

/-- Two morphisms to `(X/S)_2` agreeing after each of the three vertex projections are equal. -/
lemma two_hom_ext {T : Scheme.{u}} {a b : T ⟶ (simplicialScheme f).obj (op ⦋2⦌)}
    (h₀ : a ≫ proj f 2 0 = b ≫ proj f 2 0) (h₁ : a ≫ proj f 2 1 = b ≫ proj f 2 1)
    (h₂ : a ≫ proj f 2 2 = b ≫ proj f 2 2) : a = b := by
  refine hom_ext f (fun k => ?_)
  fin_cases k
  · exact h₀
  · exact h₁
  · exact h₂

/-- The degree-two part of `(X/S)_•` is a chosen fibre product of the degree-one part with
itself over `X`, through the faces `δ²₂` and `δ²₀`. -/
abbrev cechChosenPullbackTwo :
    ChosenPullback (cechChosenPullback f).p₂ (cechChosenPullback f).p₁ where
  pullback := (simplicialScheme f).obj (op ⦋1 + 1⦌)
  p₁ := (simplicialScheme f).map (SimplexCategory.δ (2 : Fin 3)).op
  p₂ := (simplicialScheme f).map (SimplexCategory.δ (0 : Fin 3)).op
  condition := by rw [cech_delta_two_proj_one, cech_delta_zero_proj_zero]
  isLimit := PullbackCone.IsLimit.mk _
    (fun s => triSimplex f (s.fst ≫ proj f 1 0) (s.fst ≫ proj f 1 1) (s.snd ≫ proj f 1 1)
      (by simp) (by rw [s.condition]; simp))
    (fun s => by
      refine one_hom_ext f ?_ ?_
      · rw [Category.assoc, cech_delta_two_proj_zero, triSimplex_proj_zero]
      · rw [Category.assoc, cech_delta_two_proj_one, triSimplex_proj_one])
    (fun s => by
      refine one_hom_ext f ?_ ?_
      · rw [Category.assoc, cech_delta_zero_proj_zero, triSimplex_proj_one]
        exact s.condition
      · rw [Category.assoc, cech_delta_zero_proj_one, triSimplex_proj_two])
    (fun s m h₁ h₂ => by
      refine two_hom_ext f ?_ ?_ ?_
      · rw [triSimplex_proj_zero, ← h₁, Category.assoc, cech_delta_two_proj_zero]
      · rw [triSimplex_proj_one, ← h₁, Category.assoc, cech_delta_two_proj_one]
      · rw [triSimplex_proj_two, ← h₂, Category.assoc, cech_delta_zero_proj_one])

/-- The degree-two part of `(X/S)_•` as a chosen triple fibre product of `f`, the three
projections to `(X/S)_1` being the faces `δ²₂`, `δ²₀` and `δ²₁`. -/
abbrev cechChosenPullback₃ :
    ChosenPullback₃ (cechChosenPullback f) (cechChosenPullback f) (cechChosenPullback f) where
  chosenPullback := cechChosenPullbackTwo f
  l :=
    { f := (simplicialScheme f).map (SimplexCategory.δ (1 : Fin 3)).op
      f_p₁ := by
        change _ ≫ proj f 1 0 = _ ≫ proj f 1 0
        rw [cech_delta_one_proj_zero, cech_delta_two_proj_zero]
      f_p₂ := by
        change _ ≫ proj f 1 1 = _ ≫ proj f 1 1
        rw [cech_delta_one_proj_one, cech_delta_zero_proj_one]
      f_p := by
        change _ ≫ baseMap f 1 = _ ≫ baseMap f 1
        rw [← proj_comp f 1 0, ← Category.assoc, ← Category.assoc, cech_delta_one_proj_zero,
          cech_delta_two_proj_zero] }

/-! ### `pullHom` of the module pseudofunctor as reindexing -/

open Pseudofunctor.LocallyDiscreteOpToCat in
/-- `pullHom` for the pullback pseudofunctor of sheaves of modules is the reindexing
`Stacks.Groupoids.reindexHom`, read through the comparisons of pullbacks along the two equal
composites. -/
theorem pullHom_modulePullbackPseudofunctor {T Y Z : Scheme.{u}} {t s : Y ⟶ Z}
    {M : Z.Modules}
    (γ : (Scheme.Modules.pullback t).obj M ⟶ (Scheme.Modules.pullback s).obj M)
    (p : T ⟶ Y) (g₁ g₂ : T ⟶ Z) (h₁ : p ≫ t = g₁) (h₂ : p ≫ s = g₂) :
    pullHom (F := modulePullbackPseudofunctor) (M₁ := M) (M₂ := M) γ p g₁ g₂ h₁ h₂ =
      (Scheme.Modules.pullbackCongr h₁.symm).hom.app M ≫ Stacks.Groupoids.reindexHom p γ ≫
        (Scheme.Modules.pullbackCongr h₂).hom.app M := by
  subst h₁ h₂
  rw [show (Scheme.Modules.pullbackCongr (rfl : p ≫ t = p ≫ t)).hom.app M = 𝟙 _ from rfl,
    show (Scheme.Modules.pullbackCongr (rfl : p ≫ s = p ≫ s)).hom.app M = 𝟙 _ from rfl,
    Category.id_comp, Category.comp_id]
  rfl

/-- A sheaf of modules on a scheme, as the pullback pseudofunctor spells it, read as a sheaf of
modules on the scheme. -/
def toSch {A : Scheme.{u}} (M : modulePullbackPseudofunctor.obj (.mk (op A))) : A.Modules := M

/-- A morphism between two pullbacks of sheaves of modules, as the pullback pseudofunctor spells
it, read as a morphism between the pullbacks of sheaves of modules on schemes. -/
def schemeHom {T A B : Scheme.{u}} {a : T ⟶ A} {b : T ⟶ B}
    {M : modulePullbackPseudofunctor.obj (.mk (op A))}
    {N : modulePullbackPseudofunctor.obj (.mk (op B))}
    (φ : (modulePullbackPseudofunctor.map a.op.toLoc).toFunctor.obj M ⟶
      (modulePullbackPseudofunctor.map b.op.toLoc).toFunctor.obj N) :
    (Scheme.Modules.pullback a).obj (toSch M) ⟶ (Scheme.Modules.pullback b).obj (toSch N) := φ

/-- `schemeHom` is injective. -/
theorem schemeHom_injective {T A B : Scheme.{u}} {a : T ⟶ A} {b : T ⟶ B}
    {M : modulePullbackPseudofunctor.obj (.mk (op A))}
    {N : modulePullbackPseudofunctor.obj (.mk (op B))}
    {φ ψ : (modulePullbackPseudofunctor.map a.op.toLoc).toFunctor.obj M ⟶
      (modulePullbackPseudofunctor.map b.op.toLoc).toFunctor.obj N} :
    schemeHom φ = schemeHom ψ ↔ φ = ψ := Iff.rfl

/-- `schemeHom` preserves composition. -/
theorem schemeHom_comp {T A B C : Scheme.{u}} {a : T ⟶ A} {b : T ⟶ B} {c : T ⟶ C}
    {M : modulePullbackPseudofunctor.obj (.mk (op A))}
    {N : modulePullbackPseudofunctor.obj (.mk (op B))}
    {P : modulePullbackPseudofunctor.obj (.mk (op C))}
    (φ : (modulePullbackPseudofunctor.map a.op.toLoc).toFunctor.obj M ⟶
      (modulePullbackPseudofunctor.map b.op.toLoc).toFunctor.obj N)
    (ψ : (modulePullbackPseudofunctor.map b.op.toLoc).toFunctor.obj N ⟶
      (modulePullbackPseudofunctor.map c.op.toLoc).toFunctor.obj P) :
    schemeHom (φ ≫ ψ) = schemeHom φ ≫ schemeHom ψ := rfl

/-- `schemeHom` of an isomorphism is an isomorphism. -/
instance isIso_schemeHom {T A B : Scheme.{u}} {a : T ⟶ A} {b : T ⟶ B}
    {M : modulePullbackPseudofunctor.obj (.mk (op A))}
    {N : modulePullbackPseudofunctor.obj (.mk (op B))}
    (φ : (modulePullbackPseudofunctor.map a.op.toLoc).toFunctor.obj M ⟶
      (modulePullbackPseudofunctor.map b.op.toLoc).toFunctor.obj N) [IsIso φ] :
    IsIso (schemeHom φ) :=
  ⟨schemeHom (inv φ), by rw [← schemeHom_comp, IsIso.hom_inv_id]; rfl,
    by rw [← schemeHom_comp, IsIso.inv_hom_id]; rfl⟩

open Pseudofunctor.LocallyDiscreteOpToCat in
/-- `pullHom` of the module pseudofunctor, read through `schemeHom`, is reindexing. -/
theorem schemeHom_pullHom {T Y Z : Scheme.{u}} {t s : Y ⟶ Z}
    {M : modulePullbackPseudofunctor.obj (.mk (op Z))}
    (γ : (modulePullbackPseudofunctor.map t.op.toLoc).toFunctor.obj M ⟶
      (modulePullbackPseudofunctor.map s.op.toLoc).toFunctor.obj M)
    (p : T ⟶ Y) (g₁ g₂ : T ⟶ Z) (h₁ : p ≫ t = g₁) (h₂ : p ≫ s = g₂) :
    schemeHom (pullHom γ p g₁ g₂ h₁ h₂) =
      (Scheme.Modules.pullbackCongr h₁.symm).hom.app (toSch M) ≫
        Stacks.Groupoids.reindexHom p (schemeHom γ) ≫
        (Scheme.Modules.pullbackCongr h₂).hom.app (toSch M) :=
  pullHom_modulePullbackPseudofunctor (schemeHom γ) p g₁ g₂ h₁ h₂

/-! ### The cocycle condition of a transported datum -/

section Cocycle

open Pseudofunctor.LocallyDiscreteOpToCat Stacks.Groupoids

/-- The face `δ¹₁` followed by the vertex projection is `𝟙 _ ≫ proj f 1 0`. -/
lemma delta_one_proj_zero_id :
    (simplicialScheme f).map (SimplexCategory.δ (1 : Fin 2)).op ≫ proj f 0 0 =
      𝟙 _ ≫ proj f 1 0 := by
  rw [Category.id_comp]; exact delta_one_proj f

/-- The face `δ¹₀` followed by the vertex projection is `𝟙 _ ≫ proj f 1 1`. -/
lemma delta_zero_proj_zero_id :
    (simplicialScheme f).map (SimplexCategory.δ (0 : Fin 2)).op ≫ proj f 0 0 =
      𝟙 _ ≫ proj f 1 1 := by
  rw [Category.id_comp]; exact delta_zero_proj f

variable {f}

/-- The morphism `d¹_1^* pr^* M ⟶ d¹_0^* pr^* M` on `(X/S)_1` transported from a morphism
`pr_0^* M ⟶ pr_1^* M`, where `pr : (X/S)_0 ⟶ X` is the vertex. -/
abbrev cechTransport {M : X.Modules}
    (γ : (Scheme.Modules.pullback (proj f 1 0)).obj M ⟶
      (Scheme.Modules.pullback (proj f 1 1)).obj M) :
    (Scheme.Modules.pullback ((simplicialScheme f).map (SimplexCategory.δ (1 : Fin 2)).op)).obj
        ((Scheme.Modules.pullback (proj f 0 0)).obj M) ⟶
      (Scheme.Modules.pullback ((simplicialScheme f).map (SimplexCategory.δ (0 : Fin 2)).op)).obj
        ((Scheme.Modules.pullback (proj f 0 0)).obj M) :=
  transportHom (delta_one_proj_zero_id f) (delta_zero_proj_zero_id f) γ

/-- The pair on `(X/S)_•` transported from an isomorphism `γ : pr_0^* M ⟶ pr_1^* M` satisfies the
cocycle condition if and only if `γ` satisfies the reindexed cocycle condition along the faces of
`(X/S)_2`. -/
theorem isCocycle_cechTransport_iff_reindexCocycle {M : X.Modules}
    (γ : (Scheme.Modules.pullback (proj f 1 0)).obj M ⟶
      (Scheme.Modules.pullback (proj f 1 1)).obj M) [IsIso γ] :
    (zariskiModuleFamily (simplicialScheme f)).IsCocycle
        ((Scheme.Modules.pullback (proj f 0 0)).obj M) (asIso (cechTransport γ)) ↔
      ReindexCocycle ((simplicialScheme f).map (SimplexCategory.δ (0 : Fin 3)).op)
        ((simplicialScheme f).map (SimplexCategory.δ (1 : Fin 3)).op)
        ((simplicialScheme f).map (SimplexCategory.δ (2 : Fin 3)).op) (proj f 1 1) (proj f 1 0)
        (by rw [cech_delta_two_proj_zero, cech_delta_one_proj_zero])
        (by rw [cech_delta_two_proj_one, cech_delta_zero_proj_zero])
        (by rw [cech_delta_zero_proj_one, cech_delta_one_proj_one]) γ := by
  rw [isCocycle_iff_reindexCocycle, asIso_hom]
  rw [reindexCocycle_transportHom_iff _ _ _ (delta_one_proj_zero_id f)
    (delta_zero_proj_zero_id f) γ _ _ _
    (by simp only [Category.comp_id, cech_delta_two_proj_zero, cech_delta_one_proj_zero])
    (by simp only [Category.comp_id, cech_delta_two_proj_one, cech_delta_zero_proj_zero])
    (by simp only [Category.comp_id, cech_delta_zero_proj_one, cech_delta_one_proj_one])]
  exact reindexCocycle_congr (Category.comp_id _) (Category.comp_id _) (Category.comp_id _) _ _ _
    _ _ _ γ

end Cocycle

/-! ### A conjugation identity -/

section Conj

variable {𝒞 : Type*} [Category 𝒞]

/-- Two forms of a cocycle identity among three morphisms `R₁₂`, `R₂₃`, `R₁₃`, conjugated by
isomorphisms, agree. -/
theorem conj_cocycle_iff {A A₁ B₁ B B₂ C₂ D A₃ C₃ : 𝒞} (a : A ⟶ A₁) (R₁₂ : A₁ ⟶ B₁)
    (b : B₁ ⟶ B) (c : B ⟶ B₂) (R₂₃ : B₂ ⟶ C₂) (d : C₂ ⟶ D) (e : A ⟶ A₃) [IsIso e]
    (R₁₃ : A₃ ⟶ C₃) (k : C₃ ⟶ D) [IsIso k] (x : A₃ ⟶ A₁) (y : B₁ ⟶ B₂) (z : C₂ ⟶ C₃)
    (hx : e ≫ x = a) (hy : b ≫ c = y) (hz : d = z ≫ k) :
    (a ≫ R₁₂ ≫ b) ≫ (c ≫ R₂₃ ≫ d) = e ≫ R₁₃ ≫ k ↔
      R₁₃ = x ≫ R₁₂ ≫ y ≫ R₂₃ ≫ z := by
  subst hx hy hz
  simp only [Category.assoc]
  rw [cancel_epi, show x ≫ R₁₂ ≫ b ≫ c ≫ R₂₃ ≫ z ≫ k =
    (x ≫ R₁₂ ≫ b ≫ c ≫ R₂₃ ≫ z) ≫ k by simp only [Category.assoc], cancel_mono]
  exact eq_comm

end Conj

/-! ### The cocycle condition of `DescentData'` in reindexed form -/

section GenericPseudofunctor

open Pseudofunctor.LocallyDiscreteOpToCat Pseudofunctor.DescentData'

variable {𝒞 : Type*} [Category 𝒞] (F : Pseudofunctor (LocallyDiscrete 𝒞ᵒᵖ) Cat)
  {ι : Type*} {S' : 𝒞} {Y : ι → 𝒞} {g : ∀ i, Y i ⟶ S'}
  (sq : ∀ i j, ChosenPullback (g i) (g j))
  (sq₃ : ∀ i₁ i₂ i₃, ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))

/-- The cocycle condition of a descent datum over chosen fibre products, with the three
pullbacks written through the three projections `p₁₂`, `p₂₃`, `p₁₃` of the chosen triple
product. -/
theorem pullHom'_comp_iff_pullHom (i : ι) (obj : ∀ i, F.obj (.mk (op (Y i))))
    (hom : ∀ i j, (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
      (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j)) :
    pullHom' (sq := sq) hom (sq₃ i i i).p (sq₃ i i i).p₁ (sq₃ i i i).p₂ ≫
        pullHom' (sq := sq) hom (sq₃ i i i).p (sq₃ i i i).p₂ (sq₃ i i i).p₃ =
      pullHom' (sq := sq) hom (sq₃ i i i).p (sq₃ i i i).p₁ (sq₃ i i i).p₃ ↔
    pullHom (hom i i) (sq₃ i i i).p₁₂ (sq₃ i i i).p₁ (sq₃ i i i).p₂
        (ChosenPullback₃.p₁₂_p₁ _) (ChosenPullback₃.p₁₂_p₂ _) ≫
      pullHom (hom i i) (sq₃ i i i).p₂₃ (sq₃ i i i).p₂ (sq₃ i i i).p₃
        (ChosenPullback₃.p₂₃_p₂ _) (ChosenPullback₃.p₂₃_p₃ _) =
      pullHom (hom i i) (sq₃ i i i).p₁₃ (sq₃ i i i).p₁ (sq₃ i i i).p₃
        (ChosenPullback₃.p₁₃_p₁ _) (ChosenPullback₃.p₁₃_p₃ _) := by
  rw [pullHom'₁₂_eq_pullHom_of_chosenPullback₃, pullHom'₂₃_eq_pullHom_of_chosenPullback₃,
    pullHom'₁₃_eq_pullHom_of_chosenPullback₃]

variable {F sq sq₃} in
/-- The cocycle condition of a descent datum over chosen fibre products, at an index repeated
three times, written through the three projections of the chosen triple product. -/
theorem _root_.CategoryTheory.Pseudofunctor.DescentData'.pullHom_comp_eq
    (D : F.DescentData' sq sq₃) (i : ι) :
    pullHom (D.hom i i) (sq₃ i i i).p₁₂ (sq₃ i i i).p₁ (sq₃ i i i).p₂
        (ChosenPullback₃.p₁₂_p₁ _) (ChosenPullback₃.p₁₂_p₂ _) ≫
      pullHom (D.hom i i) (sq₃ i i i).p₂₃ (sq₃ i i i).p₂ (sq₃ i i i).p₃
        (ChosenPullback₃.p₂₃_p₂ _) (ChosenPullback₃.p₂₃_p₃ _) =
      pullHom (D.hom i i) (sq₃ i i i).p₁₃ (sq₃ i i i).p₁ (sq₃ i i i).p₃
        (ChosenPullback₃.p₁₃_p₁ _) (ChosenPullback₃.p₁₃_p₃ _) :=
  (pullHom'_comp_iff_pullHom F sq sq₃ i D.obj D.hom).1 (D.pullHom'_hom_comp i i i)

/-- If the transitions of a descent datum over chosen fibre products are isomorphisms satisfying
the cocycle condition over the chosen triple products, their pullback along the diagonal is the
identity. -/
theorem pullHom'_hom_self_of_comp (obj : ∀ i, F.obj (.mk (op (Y i))))
    (hom : ∀ i j, (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
      (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j)) [hiso : ∀ i j, IsIso (hom i j)]
    (hom_comp : ∀ i₁ i₂ i₃ : ι,
      pullHom' (sq := sq) hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
        pullHom' (sq := sq) hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
      pullHom' (sq := sq) hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃) (i : ι) :
    pullHom' (sq := sq) hom (g i) (𝟙 (Y i)) (𝟙 (Y i)) = 𝟙 _ := by
  have h := comp_pullHom'' (sq₃ := sq₃) hom hom_comp (g i) (𝟙 (Y i)) (𝟙 (Y i)) (𝟙 (Y i))
    (by simp) (by simp) (by simp)
  have : IsIso (pullHom' (sq := sq) hom (g i) (𝟙 (Y i)) (𝟙 (Y i))) := by
    unfold pullHom' pullHom
    infer_instance
  exact (cancel_mono _).1 (h.trans (Category.id_comp _).symm)

/-- The cocycle condition of a descent datum over chosen fibre products from its form through
the projections of the chosen triple product, when the index type has one element. -/
theorem pullHom'_hom_comp_of_pullHom [Subsingleton ι] (obj : ∀ i, F.obj (.mk (op (Y i))))
    (hom : ∀ i j, (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
      (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j))
    (h : ∀ i, pullHom (hom i i) (sq₃ i i i).p₁₂ (sq₃ i i i).p₁ (sq₃ i i i).p₂
        (ChosenPullback₃.p₁₂_p₁ _) (ChosenPullback₃.p₁₂_p₂ _) ≫
      pullHom (hom i i) (sq₃ i i i).p₂₃ (sq₃ i i i).p₂ (sq₃ i i i).p₃
        (ChosenPullback₃.p₂₃_p₂ _) (ChosenPullback₃.p₂₃_p₃ _) =
      pullHom (hom i i) (sq₃ i i i).p₁₃ (sq₃ i i i).p₁ (sq₃ i i i).p₃
        (ChosenPullback₃.p₁₃_p₁ _) (ChosenPullback₃.p₁₃_p₃ _)) (i₁ i₂ i₃ : ι) :
    pullHom' (sq := sq) hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₂ ≫
        pullHom' (sq := sq) hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₂ (sq₃ i₁ i₂ i₃).p₃ =
      pullHom' (sq := sq) hom (sq₃ i₁ i₂ i₃).p (sq₃ i₁ i₂ i₃).p₁ (sq₃ i₁ i₂ i₃).p₃ := by
  obtain rfl := Subsingleton.elim i₂ i₁
  obtain rfl := Subsingleton.elim i₃ i₂
  exact (pullHom'_comp_iff_pullHom F sq sq₃ i₃ obj hom).2 (h i₃)

/-- A descent datum over chosen fibre products for a family indexed by a subsingleton, from
isomorphisms satisfying the cocycle condition through the projections of the chosen triple
product. -/
@[simps]
def descentData'OfPullHom [Subsingleton ι] (obj : ∀ i, F.obj (.mk (op (Y i))))
    (hom : ∀ i j, (F.map (sq i j).p₁.op.toLoc).toFunctor.obj (obj i) ⟶
      (F.map (sq i j).p₂.op.toLoc).toFunctor.obj (obj j)) [hiso : ∀ i j, IsIso (hom i j)]
    (h : ∀ i, pullHom (hom i i) (sq₃ i i i).p₁₂ (sq₃ i i i).p₁ (sq₃ i i i).p₂
        (ChosenPullback₃.p₁₂_p₁ _) (ChosenPullback₃.p₁₂_p₂ _) ≫
      pullHom (hom i i) (sq₃ i i i).p₂₃ (sq₃ i i i).p₂ (sq₃ i i i).p₃
        (ChosenPullback₃.p₂₃_p₂ _) (ChosenPullback₃.p₂₃_p₃ _) =
      pullHom (hom i i) (sq₃ i i i).p₁₃ (sq₃ i i i).p₁ (sq₃ i i i).p₃
        (ChosenPullback₃.p₁₃_p₁ _) (ChosenPullback₃.p₁₃_p₃ _)) :
    F.DescentData' sq sq₃ where
  obj := obj
  hom := hom
  pullHom'_hom_self :=
    pullHom'_hom_self_of_comp F sq sq₃ obj hom (pullHom'_hom_comp_of_pullHom F sq sq₃ obj hom h)
  pullHom'_hom_comp := pullHom'_hom_comp_of_pullHom F sq sq₃ obj hom h

/-- A descent datum over chosen fibre products for a family with one member, from an
isomorphism satisfying the cocycle condition through the projections of the chosen triple
product. -/
def descentData'OfPUnit {Y₁ : PUnit.{1} → 𝒞} {g₁ : ∀ i, Y₁ i ⟶ S'}
    (sq : ∀ i j, ChosenPullback (g₁ i) (g₁ j))
    (sq₃ : ∀ i₁ i₂ i₃, ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))
    (obj : F.obj (.mk (op (Y₁ PUnit.unit))))
    (hom : (F.map (sq PUnit.unit PUnit.unit).p₁.op.toLoc).toFunctor.obj obj ⟶
      (F.map (sq PUnit.unit PUnit.unit).p₂.op.toLoc).toFunctor.obj obj) [IsIso hom]
    (h : pullHom hom (sq₃ PUnit.unit PUnit.unit PUnit.unit).p₁₂
        (sq₃ PUnit.unit PUnit.unit PUnit.unit).p₁ (sq₃ PUnit.unit PUnit.unit PUnit.unit).p₂
        (ChosenPullback₃.p₁₂_p₁ _) (ChosenPullback₃.p₁₂_p₂ _) ≫
      pullHom hom (sq₃ PUnit.unit PUnit.unit PUnit.unit).p₂₃
        (sq₃ PUnit.unit PUnit.unit PUnit.unit).p₂ (sq₃ PUnit.unit PUnit.unit PUnit.unit).p₃
        (ChosenPullback₃.p₂₃_p₂ _) (ChosenPullback₃.p₂₃_p₃ _) =
      pullHom hom (sq₃ PUnit.unit PUnit.unit PUnit.unit).p₁₃
        (sq₃ PUnit.unit PUnit.unit PUnit.unit).p₁ (sq₃ PUnit.unit PUnit.unit PUnit.unit).p₃
        (ChosenPullback₃.p₁₃_p₁ _) (ChosenPullback₃.p₁₃_p₃ _)) :
    F.DescentData' sq sq₃ :=
  descentData'OfPullHom F sq sq₃ (fun ⟨⟩ => obj) (fun ⟨⟩ ⟨⟩ => hom)
    (hiso := fun ⟨⟩ ⟨⟩ => inferInstanceAs (IsIso hom)) (fun ⟨⟩ => h)

/-- The object of `descentData'OfPUnit` is `obj`. -/
theorem descentData'OfPUnit_obj {Y₁ : PUnit.{1} → 𝒞} {g₁ : ∀ i, Y₁ i ⟶ S'}
    (sq : ∀ i j, ChosenPullback (g₁ i) (g₁ j))
    (sq₃ : ∀ i₁ i₂ i₃, ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))
    (obj : F.obj (.mk (op (Y₁ PUnit.unit))))
    (hom : (F.map (sq PUnit.unit PUnit.unit).p₁.op.toLoc).toFunctor.obj obj ⟶
      (F.map (sq PUnit.unit PUnit.unit).p₂.op.toLoc).toFunctor.obj obj) [IsIso hom] (h) :
    (descentData'OfPUnit F sq sq₃ obj hom h).obj PUnit.unit = obj := rfl

/-- The transition of `descentData'OfPUnit` is `hom`. -/
theorem descentData'OfPUnit_hom {Y₁ : PUnit.{1} → 𝒞} {g₁ : ∀ i, Y₁ i ⟶ S'}
    (sq : ∀ i j, ChosenPullback (g₁ i) (g₁ j))
    (sq₃ : ∀ i₁ i₂ i₃, ChosenPullback₃ (sq i₁ i₂) (sq i₂ i₃) (sq i₁ i₃))
    (obj : F.obj (.mk (op (Y₁ PUnit.unit))))
    (hom : (F.map (sq PUnit.unit PUnit.unit).p₁.op.toLoc).toFunctor.obj obj ⟶
      (F.map (sq PUnit.unit PUnit.unit).p₂.op.toLoc).toFunctor.obj obj) [IsIso hom] (h) :
    (descentData'OfPUnit F sq sq₃ obj hom h).hom PUnit.unit PUnit.unit = hom := rfl

end GenericPseudofunctor

section Generic

open Pseudofunctor.LocallyDiscreteOpToCat Stacks.Groupoids

/-- For `γ : t^* M ⟶ s^* M` on `V` and three maps `d₀ d₁ d₂ : W ⟶ V` with `d₂ ≫ t = d₁ ≫ t`,
`d₂ ≫ s = d₀ ≫ t` and `d₀ ≫ s = d₁ ≫ s`, the equation `d₂^* γ ≫ d₀^* γ = d₁^* γ` of `pullHom`s
holds exactly when the reindexed cocycle condition does. -/
theorem pullHom_comp_iff_reindexCocycle {W V Z : Scheme.{u}} {t s : V ⟶ Z}
    {M : modulePullbackPseudofunctor.obj (.mk (op Z))}
    (γ : (modulePullbackPseudofunctor.map t.op.toLoc).toFunctor.obj M ⟶
      (modulePullbackPseudofunctor.map s.op.toLoc).toFunctor.obj M)
    (d₀ d₁ d₂ : W ⟶ V) (k₁ k₂ k₃ : W ⟶ Z) (h₁ : d₂ ≫ t = k₁) (h₂ : d₂ ≫ s = k₂)
    (h₃ : d₀ ≫ t = k₂) (h₄ : d₀ ≫ s = k₃) (h₅ : d₁ ≫ t = k₁) (h₆ : d₁ ≫ s = k₃) :
    pullHom γ d₂ k₁ k₂ h₁ h₂ ≫ pullHom γ d₀ k₂ k₃ h₃ h₄ = pullHom γ d₁ k₁ k₃ h₅ h₆ ↔
      ReindexCocycle (M := toSch M) d₀ d₁ d₂ s t (h₁.trans h₅.symm) (h₂.trans h₃.symm)
        (h₄.trans h₆.symm) (schemeHom γ) := by
  rw [← schemeHom_injective, schemeHom_comp, schemeHom_pullHom, schemeHom_pullHom,
    schemeHom_pullHom]
  unfold ReindexCocycle
  exact conj_cocycle_iff _ _ _ _ _ _ ((Scheme.Modules.pullbackCongr _).hom.app (toSch M)) _
    ((Scheme.Modules.pullbackCongr _).hom.app (toSch M)) _ _ _
    (pullbackCongr_hom_app_comp _ _ _) (pullbackCongr_hom_app_comp _ _ _)
    (pullbackCongr_hom_app_comp _ _ _).symm

end Generic

end AlgebraicGeometry.SimplicialScheme
