module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Forget
public import StacksCore.Tactic.StacksAttribute

/-!
# Abelian sheaves on a topological space

Stacks 0070 defines an *abelian sheaf* on a topological space `X` to be an abelian presheaf
whose underlying presheaf of sets is a sheaf, and writes `Ab(X)` for the resulting category.

In Mathlib an abelian presheaf on `X` is a `TopCat.Presheaf AddCommGrpCat X` and the sheaf
condition `TopCat.Presheaf.IsSheaf` is imposed directly on the `AddCommGrpCat`-valued
functor rather than on the underlying presheaf of sets. That the two agree — which is what
makes the Stacks definition a definition of the same notion — is Mathlib's
`TopCat.Presheaf.isSheaf_iff_isSheaf_comp`, at the forgetful functor from abelian groups to
types, which preserves limits and reflects isomorphisms. The category `Ab(X)` is
`TopCat.Sheaf AddCommGrpCat X` with `TopCat.instCategorySheaf`; Mathlib has neither a
dedicated name nor the notation `Ab(X)`, so those two declarations are registered for the
tag directly.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

-- The former @[stacks 0070 "(1)"] theorem was this Mathlib theorem at `forget AddCommGrpCat`.
add_to_stacks 0070 "an abelian presheaf is a sheaf exactly when its underlying presheaf of
  sets is one: the sheaf condition is unchanged by composing with a limit-preserving,
  isomorphism-reflecting functor, here the forgetful functor to types."
  TopCat.Presheaf.isSheaf_iff_isSheaf_comp
add_to_sga "4 II 6.2" "special case" TopCat.Presheaf.isSheaf_iff_isSheaf_comp
add_to_sga "4 II 6.3.1" "topological space" TopCat.Presheaf.isSheaf_iff_isSheaf_comp

/- **Stacks 0070 (2).** The category `Ab(X)` of sheaves of abelian groups on `X` is
`TopCat.Sheaf AddCommGrpCat X`. Mathlib defines `TopCat.Sheaf C X` for an arbitrary target
category `C` and has no separate name, and no notation `Ab(X)`, for the abelian case. -/
add_to_stacks 0070 "Sheaves of abelian groups on `X` are the objects of
  `TopCat.Sheaf AddCommGrpCat X`; Mathlib states the sheaf condition for a general target
  category rather than naming the abelian case, and has no notation `Ab(X)`."
  TopCat.Sheaf
add_to_sga "3 IV 4.3.1" "special case" TopCat.Sheaf
add_to_sga "3 IV 4.3.18" "special case" TopCat.Sheaf
add_to_sga "4 II 6.1" "special case" TopCat.Sheaf
add_to_sga "4 IV 0.1" "special case" TopCat.Sheaf
add_to_sga "4 IV 2.1" TopCat.Sheaf
add_to_sga "4 VI 1.22.1" TopCat.Sheaf
add_to_sga "4 Vbis 4.2.0" "Fiber of E over a scheme" TopCat.Sheaf
add_to_sga "4½ Arcata 1.2.3" "more general" TopCat.Sheaf
add_to_ega "0 3.1.4" TopCat.Sheaf

/- The category structure on `Ab(X)`, i.e. the second half of Stacks 0070 (2): morphisms of
abelian sheaves are morphisms of the underlying abelian presheaves. -/
add_to_stacks 0070 "The category structure on `Ab(X) = TopCat.Sheaf AddCommGrpCat X`,
  derived from the category of sheaves on the site of opens of `X`."
  TopCat.instCategorySheaf
add_to_sga "3 IV 4.3.1" "special case" TopCat.instCategorySheaf
add_to_sga "4 II 6.1" "special case" TopCat.instCategorySheaf
add_to_sga "4 IV 0.1" "special case" TopCat.instCategorySheaf
add_to_sga "4 IV 2.1" "partial" TopCat.instCategorySheaf

namespace TopCat.Sheaf

/-- A morphism `g` is epi as soon as the complex `g, 0` is exact. -/
private theorem epi_of_exact_mk_zero {X : TopCat.{u}} {A B : TopCat.Sheaf AddCommGrpCat.{u} X}
    (g : A ⟶ B) (h : (ShortComplex.mk g (0 : B ⟶ B) comp_zero).Exact) : Epi g :=
  ((ShortComplex.mk g (0 : B ⟶ B) comp_zero).exact_iff_epi rfl).1 h

/-- A short complex of abelian sheaves is short exact as soon as it is short exact on every
stalk. -/
theorem shortExact_of_stalk {X : TopCat.{u}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X))
    (h : ∀ x : X, (S.map (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).ShortExact) : S.ShortExact := by
  refine { exact := (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).2 (fun x => (h x).exact)
           mono_f := (TopCat.Presheaf.mono_iff_stalk_mono S.f).2 (fun x => (h x).mono_f)
           epi_g := epi_of_exact_mk_zero _ ?_ }
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).2
  intro x
  apply (((ShortComplex.mk S.g (0 : S.X₃ ⟶ S.X₃) comp_zero).map (TopCat.Sheaf.forget
    AddCommGrpCat.{u} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)).exact_iff_epi
    (by simp; rfl)).2
  exact (h x).epi_g

/-- A sequence of sheaves of abelian groups is exact once every section of the middle sheaf
killed by the second map is germ-locally in the image of the first. -/
theorem exact_of_local {X : TopCat.{u}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X))
    (h : ∀ (U : Opens X) (s : S.X₂.obj.obj (op U)), S.g.hom.app (op U) s = 0 →
      ∀ x ∈ U, ∃ (V : Opens X) (i : V ⟶ U) (_ : x ∈ V)
        (t : S.X₁.obj.obj (op V)), S.f.hom.app (op V) t = S.X₂.obj.map i.op s) :
    S.Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).2
  intro x
  apply (ShortComplex.ab_exact_iff _).2
  intro s hs
  obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq S.X₂.obj s
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.g.hom
    ((TopCat.Presheaf.germ S.X₂.obj) U x hx s) = 0 at hs
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at hs
  obtain ⟨V, hxV, i, j, hij⟩ := (TopCat.Presheaf.germ_eq S.X₃.obj) x hx hx
    (S.g.hom.app (op U) s) 0 (by rwa [map_zero])
  have hv : S.g.hom.app (op V) (S.X₂.obj.map i.op s) = 0 := by
    rw [← ConcreteCategory.comp_apply, S.g.hom.naturality]
    simpa using hij
  obtain ⟨W, l, hxW, t, ht⟩ := h V (S.X₂.obj.map i.op s) hv x hxV
  refine ⟨(TopCat.Presheaf.germ S.X₁.obj) W x hxW t, ?_⟩
  show (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.f.hom
    ((TopCat.Presheaf.germ S.X₁.obj) W x hxW t) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ht,
    TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]

/-- A sequence of sheaves of abelian groups is short exact once its three defining conditions
hold germ-locally: a section killed by the first map vanishes near every point, a section killed
by the second map is locally in the image of the first, and every section of the third sheaf is
locally in the image of the second.

This is the sectionwise companion of `TopCat.Sheaf.shortExact_of_stalk`. It is the form to reach
for when the third sheaf is a skyscraper and the sequence is described by its values on sections,
since then no stalk of the middle sheaf has to be computed. -/
theorem shortExact_of_local {X : TopCat.{u}}
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X))
    (hmono : ∀ (U : Opens X) (s : S.X₁.obj.obj (op U)), S.f.hom.app (op U) s = 0 →
      ∀ x ∈ U, ∃ (V : Opens X) (i : V ⟶ U) (_ : x ∈ V), S.X₁.obj.map i.op s = 0)
    (hmid : ∀ (U : Opens X) (s : S.X₂.obj.obj (op U)), S.g.hom.app (op U) s = 0 →
      ∀ x ∈ U, ∃ (V : Opens X) (i : V ⟶ U) (_ : x ∈ V)
        (t : S.X₁.obj.obj (op V)), S.f.hom.app (op V) t = S.X₂.obj.map i.op s)
    (hepi : ∀ (U : Opens X) (s : S.X₃.obj.obj (op U)),
      ∀ x ∈ U, ∃ (V : Opens X) (i : V ⟶ U) (_ : x ∈ V)
        (t : S.X₂.obj.obj (op V)), S.g.hom.app (op V) t = S.X₃.obj.map i.op s) :
    S.ShortExact := by
  refine { exact := exact_of_local S hmid, mono_f := ?_, epi_g := ?_ }
  · let T := ShortComplex.mk (0 : S.X₁ ⟶ S.X₁) S.f zero_comp
    refine (T.exact_iff_mono rfl).1 (exact_of_local T fun U s hs x hx => ?_)
    obtain ⟨V, i, hxV, hv⟩ := hmono U s hs x hx
    exact ⟨V, i, hxV, 0, by simpa [T] using hv.symm⟩
  · exact epi_of_exact_mk_zero _ (exact_of_local _ fun U s _ x hx => hepi U s x hx)

end TopCat.Sheaf

namespace TopCat.Presheaf

/-- A section of a sheaf of abelian groups whose germs vanish at every point of a smaller open
set restricts to zero on that smaller open set. -/
theorem restrict_eq_zero_of_germ_eq_zero {Y : TopCat.{u}} {P : TopCat.Presheaf Ab Y}
    (hP : TopCat.Presheaf.IsSheaf P) {W W' : Opens Y} (i : W' ⟶ W) (s : P.obj (op W))
    (h : ∀ (x : Y) (hx : x ∈ W'), P.germ W x (i.le hx) s = 0) :
    P.map i.op s = 0 := by
  refine TopCat.Presheaf.section_ext ⟨P, hP⟩ W' _ 0 fun x hx => ?_
  show P.germ W' x hx (P.map i.op s) = P.germ W' x hx 0
  rw [map_zero, TopCat.Presheaf.germ_res_apply]
  exact h x hx

end TopCat.Presheaf
