module

public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder.Stalk

/-!
# A section which is a stalk basis everywhere trivializes the module

Let `L` be an `𝒪_X`-module and `e` a section of `L` over an open `W` whose germ at every point of
`W` is a stalk basis, that is, multiplication by it is a bijection `𝒪_{X, y} ⟶ L_y`. Then for every
open `V ⊆ W` multiplication by the restriction of `e` is a bijection `Γ(X, V) ⟶ Γ(L, V)`. This is
the converse of `Stacks.Divisors.isStalkBasis_germ_of_bijective_smul`.

## Main results

* `Stacks.Divisors.bijective_smul_of_isStalkBasis`: multiplication by the restriction of a section
  whose germs are stalk bases is bijective on sections over every smaller open.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (L : X.Modules)

/-- Restricting `c • e|_U` along `V ⟶ U` restricts both factors. -/
private theorem map_smul_map {U V W : X.Opens} (i : V ⟶ U) (hUW : U ≤ W) (c : Γ(X, U))
    (e : Γ(L, W)) : L.presheaf.map i.op (c • L.presheaf.map (homOfLE hUW).op e) =
      X.presheaf.map i.op c • L.presheaf.map (homOfLE ((leOfHom i).trans hUW)).op e := by
  rw [Scheme.Modules.map_smul, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- **A section whose germs are stalk bases is a basis over every smaller open.** If the germ of
`e : Γ(L, W)` at every point of `W` is a stalk basis of `L`, then for every open `V ≤ W`
multiplication by the restriction of `e` to `V` is a bijection `Γ(X, V) → Γ(L, V)`. -/
theorem bijective_smul_of_isStalkBasis {W : X.Opens} (e : Γ(L, W))
    (h : ∀ (y : X) (hy : y ∈ W), IsStalkBasis L y (L.presheaf.germ W y hy e)) {V : X.Opens}
    (hV : V ≤ W) :
    Function.Bijective fun c : Γ(X, V) => c • L.presheaf.map (homOfLE hV).op e := by
  have hgerm : ∀ (y : X) (hy : y ∈ V),
      L.presheaf.germ V y hy (L.presheaf.map (homOfLE hV).op e) = L.presheaf.germ W y (hV hy) e :=
    fun y hy => L.presheaf.germ_res_apply (homOfLE hV) y hy e
  have hinj : ∀ (V' : X.Opens) (hV' : V' ≤ W) (c c' : Γ(X, V')),
      c • L.presheaf.map (homOfLE hV').op e = c' • L.presheaf.map (homOfLE hV').op e →
        c = c' := by
    intro V' hV' c c' hcc'
    refine TopCat.Presheaf.section_ext X.sheaf V' c c' fun y hy => ?_
    have h1 := congrArg (L.presheaf.germ V' y hy) hcc'
    rw [Scheme.Modules.germ_smul L hy, Scheme.Modules.germ_smul L hy,
      L.presheaf.germ_res_apply (homOfLE hV') y hy e] at h1
    exact (h y (hV' hy)).injective h1
  refine ⟨fun c c' hcc' => hinj V hV c c' hcc', fun s => ?_⟩
  have hloc : ∀ y : V, ∃ (U : X.Opens) (hyU : y.1 ∈ U) (hUV : U ≤ V) (c : Γ(X, U)),
      c • L.presheaf.map (homOfLE (hUV.trans hV)).op e = L.presheaf.map (homOfLE hUV).op s := by
    intro ⟨y, hy⟩
    obtain ⟨r, hr⟩ := (h y (hV hy)).surjective (L.presheaf.germ V y hy s)
    obtain ⟨U₀, hyU₀, c₀, hc₀⟩ := X.presheaf.exists_germ_eq r
    have hyU₁ : y ∈ U₀ ⊓ V := ⟨hyU₀, hy⟩
    have hU₁V : U₀ ⊓ V ≤ V := inf_le_right
    set c₁ : Γ(X, U₀ ⊓ V) := X.presheaf.map (homOfLE inf_le_left).op c₀ with hc₁
    have hgs : L.presheaf.germ (U₀ ⊓ V) y hyU₁
        (c₁ • L.presheaf.map (homOfLE (hU₁V.trans hV)).op e) =
        L.presheaf.germ (U₀ ⊓ V) y hyU₁ (L.presheaf.map (homOfLE hU₁V).op s) := by
      rw [Scheme.Modules.germ_smul L hyU₁, L.presheaf.germ_res_apply, L.presheaf.germ_res_apply,
        hc₁, X.presheaf.germ_res_apply, hc₀]
      exact hr
    obtain ⟨U, hyU, i₁, i₂, hU⟩ := L.presheaf.germ_eq y hyU₁ hyU₁ _ _ hgs
    have hUV : U ≤ V := (leOfHom i₁).trans hU₁V
    refine ⟨U, hyU, hUV, X.presheaf.map i₁.op c₁, ?_⟩
    rw [map_smul_map, Subsingleton.elim i₂ i₁] at hU
    refine hU.trans ?_
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  choose U hyU hUV c hc using hloc
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 U c := by
    intro i j
    refine hinj (U i ⊓ U j) ((inf_le_left.trans (hUV i)).trans hV) _ _ ?_
    have hi := congrArg (L.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op) (hc i)
    have hj := congrArg (L.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op) (hc j)
    rw [map_smul_map, ← ConcreteCategory.comp_apply, ← Functor.map_comp] at hi hj
    exact hi.trans hj.symm
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf U V (fun i => homOfLE (hUV i))
    (fun y hy => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hyU ⟨y, hy⟩⟩) c hcompat
  refine ⟨(show Γ(X, V) from g), ?_⟩
  refine TopCat.Presheaf.section_ext ⟨L.presheaf, L.isSheaf⟩ V _ s fun y hy => ?_
  have hy' := hyU ⟨y, hy⟩
  have e1 := congrArg (L.presheaf.germ (U ⟨y, hy⟩) y hy') (hc ⟨y, hy⟩)
  rw [L.presheaf.germ_res_apply, Scheme.Modules.germ_smul L hy', L.presheaf.germ_res_apply,
    ← hg ⟨y, hy⟩] at e1
  have e2 : X.presheaf.germ (U ⟨y, hy⟩) y hy' (X.presheaf.map (homOfLE (hUV ⟨y, hy⟩)).op g) =
      X.presheaf.germ V y hy g := X.presheaf.germ_res_apply _ y hy' g
  rw [show X.sheaf.obj.map (homOfLE (hUV ⟨y, hy⟩)).op g =
    X.presheaf.map (homOfLE (hUV ⟨y, hy⟩)).op g from rfl, e2] at e1
  change L.presheaf.germ V y hy ((show Γ(X, V) from g) • L.presheaf.map (homOfLE hV).op e) = _
  rw [Scheme.Modules.germ_smul L hy, hgerm]
  exact e1

end Stacks.Divisors
