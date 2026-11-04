module

public import StacksFrontier.Topology.Sheaves.Stalk.PullbackAdjointStalk
public import StacksFrontier.Topology.Simplicial.Augmentation

/-!
# Germs and the transition maps of a simplicial sheaf system

Let `Z` be a simplicial topological space and `S` a system of sheaves of sets on the spaces
`Z_n` with transition maps along the simplicial structure maps, as in Tag 09VM. For
`φ : n ⟶ m` in `Δᵒᵖ` the transition map of `S` sends a section of `S_m` over `V` to a section of
`S_n` over `Z(φ)⁻¹(V)`; on stalks it induces maps `(S_m)_{Z(φ)(w)} → (S_n)_w`.

This file records how these act on germs: the germ of a transported section only depends on the
germ of the section, transport along an identity does not change germs, and transport along a
composite is the composite of the transports. The stalk maps are bijective as soon as the
adjoint of the transition map is an isomorphism, which is the cartesian condition.

## Main definitions

* `Stacks.Topology.Simplicial.SimplicialSheafSystem.stalkTransition`: the map
  `(S_m)_{Z(φ)(w)} → (S_n)_w` induced by a transition map.

## Main results

* `stalkTransition_germ`: the stalk map sends the germ of `s` to the germ of its transport.
* `germ_transition_id` and `germ_transition_comp`: germs of transports along identities and
  composites.
* `bijective_stalkTransition`: the stalk maps of a transition whose adjoint is an isomorphism
  are bijective.

## References

* [Stacks Project, Tag 09VM](https://stacks.math.columbia.edu/tag/09VM)
* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.Topology.Simplicial.SimplicialSheafSystem

variable {Z : SimplicialObject TopCat.{u}} (S : SimplicialSheafSystem Z (Type u))

/-- Germs of sections over equal opens which are equal up to the identification of the two
section types are equal. -/
theorem germ_eq_of_heq {T : TopCat.{u}} (F : T.Presheaf (Type u)) {V V' : Opens T}
    (e : V = V') {s : F.obj (op V)} {s' : F.obj (op V')} (h : HEq s s') (x : T) (hx : x ∈ V)
    (hx' : x ∈ V') : F.germ V x hx s = F.germ V' x hx' s' := by
  subst e
  cases h
  rfl

/-- Two morphisms of types which agree up to an identification of their targets send each
element to elements which agree up to that identification. -/
theorem heq_apply_of_heq {A B B' : Type u} (e : B = B') {f : A ⟶ B} {g : A ⟶ B'} (h : HEq f g)
    (a : A) : HEq (f a) (g a) := by
  subst e
  cases h
  rfl

/-- The map on stalks `(S_m)_{Z(φ)(w)} → (S_n)_w` induced by the transition map of `S`
along `φ : n ⟶ m`. -/
noncomputable def stalkTransition {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (w : Z.obj n) :
    (S.component m).presheaf.stalk (Z.map φ w) ⟶ (S.component n).presheaf.stalk w :=
  Stacks.Sheaves.PullbackUnit.stalkComparison (Z.map φ) (Type u) (S.transition φ).toPresheafHom w

/-- The stalk map of a transition sends the germ of a section to the germ of its transport. -/
theorem stalkTransition_germ {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (w : Z.obj n)
    (V : Opens (Z.obj m)) (hw : Z.map φ w ∈ V) (s : (S.component m).presheaf.obj (op V)) :
    S.stalkTransition φ w ((S.component m).presheaf.germ V _ hw s) =
      (S.component n).presheaf.germ ((Opens.map (Z.map φ)).obj V) w hw
        ((S.transition φ).app (op V) s) :=
  ConcreteCategory.congr_hom
    (Stacks.Sheaves.PullbackUnit.germ_stalkComparison (Z.map φ) (Type u)
      (S.transition φ).toPresheafHom w V hw) s

/-- Germs of images of one element under morphisms into sections over equal opens, which are equal
up to the identification of the targets, are equal. -/
private theorem germ_apply_eq_of_heq {T : TopCat.{u}} (F : T.Presheaf (Type u)) {V V' : Opens T}
    (e : V = V') {A : Type u} {f : A ⟶ F.obj (op V)} {g : A ⟶ F.obj (op V')} (h : HEq f g)
    (a : A) (x : T) (hx : x ∈ V) (hx' : x ∈ V') : F.germ V x hx (f a) = F.germ V' x hx' (g a) := by
  subst e
  cases h
  rfl

/-- The germ of a transported section only depends on the germ of the section. -/
theorem germ_transition_congr {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (w : Z.obj n)
    {V V' : Opens (Z.obj m)} (hw : Z.map φ w ∈ V) (hw' : Z.map φ w ∈ V')
    {s : (S.component m).presheaf.obj (op V)} {s' : (S.component m).presheaf.obj (op V')}
    (h : (S.component m).presheaf.germ V _ hw s = (S.component m).presheaf.germ V' _ hw' s') :
    (S.component n).presheaf.germ ((Opens.map (Z.map φ)).obj V) w hw
        ((S.transition φ).app (op V) s) =
      (S.component n).presheaf.germ ((Opens.map (Z.map φ)).obj V') w hw'
        ((S.transition φ).app (op V') s') := by
  rw [← stalkTransition_germ, ← stalkTransition_germ, h]

/-- Transport along an identity does not change germs. -/
theorem germ_transition_id (n : SimplexCategoryᵒᵖ) (w : Z.obj n) (V : Opens (Z.obj n))
    (hw : Z.map (𝟙 n) w ∈ V) (hw' : w ∈ V) (s : (S.component n).presheaf.obj (op V)) :
    (S.component n).presheaf.germ ((Opens.map (Z.map (𝟙 n))).obj V) w hw
        ((S.transition (𝟙 n)).app (op V) s) =
      (S.component n).presheaf.germ V w hw' s := by
  have e : (Opens.map (Z.map (𝟙 n))).obj V = V := by simp
  exact germ_apply_eq_of_heq _ e (S.transition_id n (op V)) s w hw hw'

/-- Transport along a composite is the composite of the transports, on germs. -/
theorem germ_transition_comp {l m n : SimplexCategoryᵒᵖ} (φ : l ⟶ m) (ψ : m ⟶ n)
    (w : Z.obj l) (V : Opens (Z.obj n)) (hw : Z.map ψ (Z.map φ w) ∈ V)
    (hw' : Z.map (φ ≫ ψ) w ∈ V) (s : (S.component n).presheaf.obj (op V)) :
    (S.component l).presheaf.germ ((Opens.map (Z.map φ)).obj ((Opens.map (Z.map ψ)).obj V)) w
        hw ((S.transition φ).app (op ((Opens.map (Z.map ψ)).obj V))
          ((S.transition ψ).app (op V) s)) =
      (S.component l).presheaf.germ ((Opens.map (Z.map (φ ≫ ψ))).obj V) w hw'
        ((S.transition (φ ≫ ψ)).app (op V) s) := by
  have e : (Opens.map (Z.map φ)).obj ((Opens.map (Z.map ψ)).obj V) =
      (Opens.map (Z.map (φ ≫ ψ))).obj V := by
    rw [Z.map_comp]
    rfl
  exact germ_apply_eq_of_heq _ e (S.transition_comp φ ψ (op V)) s w hw hw'

/-- The stalk maps of a transition map whose adjoint is an isomorphism are bijective. -/
theorem bijective_stalkTransition {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m)
    (h : IsIso (((Augmentation.adj (Z.map φ)).homEquiv _ _).symm
      (Augmentation.systemTransition Z S φ))) (w : Z.obj n) :
    Function.Bijective (S.stalkTransition φ w) :=
  (Stacks.Sheaves.PullbackUnit.isIso_homEquiv_symm_iff (Z.map φ) _).1 h w

/-! ### Transport of germs -/

/-- `h` at `q ∈ Z_m` is carried to `k` at `w ∈ Z_n` by the transition map along `φ`: some section
with germ `h` at `q` has a transport with germ `k` at `w`. This is meaningful when
`Z(φ)(w) = q`, and then it is the graph of `stalkTransition φ w`
(`germTransport_iff_stalkTransition`). -/
def GermTransport {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (w : Z.obj n) (q : Z.obj m)
    (h : (S.component m).presheaf.stalk q) (k : (S.component n).presheaf.stalk w) : Prop :=
  ∃ (V : Opens (Z.obj m)) (hq : q ∈ V) (hw : Z.map φ w ∈ V)
    (s : (S.component m).presheaf.obj (op V)),
    (S.component m).presheaf.germ V q hq s = h ∧
      (S.component n).presheaf.germ ((Opens.map (Z.map φ)).obj V) w hw
        ((S.transition φ).app (op V) s) = k

variable {S}

/-- At `q = Z(φ)(w)`, germ transport is the graph of the stalk map of the transition. -/
theorem germTransport_iff_stalkTransition {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (w : Z.obj n)
    (h : (S.component m).presheaf.stalk (Z.map φ w)) (k : (S.component n).presheaf.stalk w) :
    S.GermTransport φ w (Z.map φ w) h k ↔ S.stalkTransition φ w h = k := by
  constructor
  · rintro ⟨V, hq, hw, s, rfl, rfl⟩
    exact S.stalkTransition_germ φ w V hq s
  · rintro rfl
    obtain ⟨V, hq, s, rfl⟩ := (S.component m).presheaf.exists_germ_eq h
    exact ⟨V, hq, hq, s, rfl, (S.stalkTransition_germ φ w V hq s).symm⟩

/-- Every germ at `Z(φ)(w)` is transported to some germ at `w`. -/
theorem exists_germTransport {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (w : Z.obj n) {q : Z.obj m}
    (hq : Z.map φ w = q) (h : (S.component m).presheaf.stalk q) :
    ∃ k, S.GermTransport φ w q h k := by
  subst hq
  exact ⟨_, (germTransport_iff_stalkTransition φ w h _).2 rfl⟩

/-- Germ transport is single-valued. -/
theorem GermTransport.unique {n m : SimplexCategoryᵒᵖ} {φ : n ⟶ m} {w : Z.obj n} {q : Z.obj m}
    (hq : Z.map φ w = q) {h : (S.component m).presheaf.stalk q}
    {k k' : (S.component n).presheaf.stalk w} (hk : S.GermTransport φ w q h k)
    (hk' : S.GermTransport φ w q h k') : k = k' := by
  subst hq
  exact ((germTransport_iff_stalkTransition φ w h k).1 hk).symm.trans
    ((germTransport_iff_stalkTransition φ w h k').1 hk')

/-- The transport of the germ of a section is the germ of its transport. -/
theorem germTransport_germ {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (w : Z.obj n)
    (V : Opens (Z.obj m)) (hw : Z.map φ w ∈ V) (s : (S.component m).presheaf.obj (op V)) :
    S.GermTransport φ w (Z.map φ w) ((S.component m).presheaf.germ V _ hw s)
      ((S.component n).presheaf.germ ((Opens.map (Z.map φ)).obj V) w hw
        ((S.transition φ).app (op V) s)) :=
  ⟨V, hw, hw, s, rfl, rfl⟩

/-- Transport along an identity is the identity. -/
theorem germTransport_id (n : SimplexCategoryᵒᵖ) (w : Z.obj n)
    (h : (S.component n).presheaf.stalk w) : S.GermTransport (𝟙 n) w w h h := by
  obtain ⟨V, hw, s, rfl⟩ := (S.component n).presheaf.exists_germ_eq h
  have hw' : Z.map (𝟙 n) w ∈ V := by simpa using hw
  exact ⟨V, hw, hw', s, rfl, S.germ_transition_id n w V hw' hw s⟩

/-- Transport along a composite is the composite of the transports. -/
theorem GermTransport.comp {l m n : SimplexCategoryᵒᵖ} {φ : l ⟶ m} {ψ : m ⟶ n} {w : Z.obj l}
    {q : Z.obj n} (_hq : Z.map ψ (Z.map φ w) = q) {h : (S.component n).presheaf.stalk q}
    {k : (S.component m).presheaf.stalk (Z.map φ w)} {k' : (S.component l).presheaf.stalk w}
    (hψ : S.GermTransport ψ (Z.map φ w) q h k) (hφ : S.GermTransport φ w (Z.map φ w) k k') :
    S.GermTransport (φ ≫ ψ) w q h k' := by
  obtain ⟨V, hqV, hwV, s, rfl, rfl⟩ := hψ
  have hw' : Z.map (φ ≫ ψ) w ∈ V := by
    rw [Z.map_comp]
    exact hwV
  refine ⟨V, hqV, hw', s, rfl, ?_⟩
  rw [← S.germ_transition_comp φ ψ w V hwV hw' s]
  exact (hφ.unique rfl (S.germTransport_germ φ w _ hwV _)).symm

/-- Transport along a transition whose adjoint is an isomorphism is injective. -/
theorem GermTransport.inj {n m : SimplexCategoryᵒᵖ} {φ : n ⟶ m}
    (hφ : IsIso (((Augmentation.adj (Z.map φ)).homEquiv _ _).symm
      (Augmentation.systemTransition Z S φ))) {w : Z.obj n} {q : Z.obj m}
    (hq : Z.map φ w = q) {h h' : (S.component m).presheaf.stalk q}
    {k : (S.component n).presheaf.stalk w} (hk : S.GermTransport φ w q h k)
    (hk' : S.GermTransport φ w q h' k) : h = h' := by
  subst hq
  exact (S.bijective_stalkTransition φ hφ w).1
    (((germTransport_iff_stalkTransition φ w h k).1 hk).trans
      ((germTransport_iff_stalkTransition φ w h' k).1 hk').symm)

/-- Transport along a transition whose adjoint is an isomorphism is surjective. -/
theorem exists_germTransport_of_isIso {n m : SimplexCategoryᵒᵖ} {φ : n ⟶ m}
    (hφ : IsIso (((Augmentation.adj (Z.map φ)).homEquiv _ _).symm
      (Augmentation.systemTransition Z S φ))) {w : Z.obj n} {q : Z.obj m}
    (hq : Z.map φ w = q) (k : (S.component n).presheaf.stalk w) :
    ∃ h, S.GermTransport φ w q h k := by
  subst hq
  obtain ⟨h, rfl⟩ := (S.bijective_stalkTransition φ hφ w).2 k
  exact ⟨h, (germTransport_iff_stalkTransition φ w h _).2 rfl⟩

end Stacks.Topology.Simplicial.SimplicialSheafSystem
