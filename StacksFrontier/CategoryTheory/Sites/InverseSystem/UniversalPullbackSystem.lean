module

public import StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.InjectiveSystemsOfAbelianSheaves

/-!
# The system of inverse images of a sheaf on the terminal level of an inverse system of sites

Let `D` be an inverse system of sites with finite coverings (Stacks 0A34) whose index category has
a terminal object `t`, so that every level `i` carries a unique transition `!ᵢ : i ⟶ t` and a
functor `u_{!ᵢ} : C_t ⥤ C_i`. A sheaf `F₀` on `C_t` has inverse images `Fᵢ = f_{!ᵢ}⁻¹F₀` on all
levels, and these form a system of sheaves in the sense of Stacks 0EXZ, with transition maps
`ψ_a : Fᵢ ⟶ f_{a,*}F_j` adjoint to the composition isomorphisms of inverse images. Its colimit on a
colimit site `C` (Stacks 09YL) is `f_t⁻¹F₀`.

This file proves those facts without ever naming an inverse-image functor: an inverse image is
characterised by the **universal arrow** `εᵢ : F₀ ⟶ u_{!ᵢ,*}Fᵢ`, and every transition map, every
cocycle condition and the colimit property is read off from the uniqueness clause of the
universal property. This keeps the statements free of the coherence isomorphisms of composite
inverse images, which is what makes them usable for both sheaves of sets and abelian sheaves, and
for inverse images presented by any construction (for instance a comparison with Mathlib's small
étale sites).

## Main definitions

* `IsUniversalArrow`: the universal property of the inverse image.
* `ψ`: the transition maps of the system, in adjoint form.
* `ι`: the structure maps of the colimit `f_t⁻¹F₀` on a colimit site.

## Main results

* `ψ_comp`: the cocycle condition of the transition maps.
* `ι_comp`: the compatibility of the structure maps with the transition maps.
* `existsUnique_of_compatible`: the colimit property.
* `isColimitPresentation_abelianSystem`: for abelian sheaves, `G` with the maps `ι` presents the
  colimit of the system `abelianSystem`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Sites.InverseSystem

universe v u w

namespace Stacks.WeakSites.PullbackSystem

/-! ### Universal arrows from adjunctions, across equivalences -/

section Transport

variable {𝒞' 𝒟' 𝒞 𝒟 : Type*} [Category 𝒞'] [Category 𝒟'] [Category 𝒞] [Category 𝒟]
  {L : 𝒟' ⥤ 𝒞'} {R' : 𝒞' ⥤ 𝒟'} (adj : L ⊣ R') (e : 𝒞' ≌ 𝒞)
  {E₀ : 𝒟' ⥤ 𝒟} (hE₀ : E₀.FullyFaithful) (R : 𝒞 ⥤ 𝒟) (β : R' ⋙ E₀ ≅ e.functor ⋙ R)

include hE₀ in
/-- **A unit of an adjunction stays a universal arrow across equivalences.** If `R` is identified
with `R'` through an equivalence `e` on one side and a fully faithful `E₀` on the other, the image
of the unit `F ⟶ R'(LF)` under `E₀`, read through the identification, is a universal arrow from
`E₀ F` to `R`. -/
theorem existsUnique_of_adjunction (F : 𝒟') (M : 𝒞) (g : E₀.obj F ⟶ R.obj M) :
    ∃! h : e.functor.obj (L.obj F) ⟶ M,
      (E₀.map (adj.unit.app F) ≫ β.hom.app (L.obj F)) ≫ R.map h = g := by
  let c : E₀.obj (R'.obj (e.inverse.obj M)) ⟶ R.obj M :=
    β.hom.app (e.inverse.obj M) ≫ R.map (e.counit.app M)
  have claim : ∀ h : e.functor.obj (L.obj F) ⟶ M,
      (E₀.map (adj.unit.app F) ≫ β.hom.app (L.obj F)) ≫ R.map h =
        E₀.map (adj.homEquiv _ _ (e.toAdjunction.homEquiv _ _ h)) ≫ c := by
    intro h
    have h1 : h = e.functor.map (e.toAdjunction.homEquiv _ _ h) ≫ e.counit.app M := by
      conv_lhs => rw [← (e.toAdjunction.homEquiv _ _).symm_apply_apply h]
      rw [Adjunction.homEquiv_counit]
      rfl
    have hn := β.hom.naturality (e.toAdjunction.homEquiv _ _ h)
    simp only [Functor.comp_map] at hn
    rw [Adjunction.homEquiv_unit, E₀.map_comp]
    simp only [c, Category.assoc]
    rw [reassoc_of% hn, ← R.map_comp, ← h1]
  have hiso : IsIso c := by
    have : IsIso (R.map (e.counit.app M)) := Functor.map_isIso R _
    infer_instance
  refine ⟨(e.toAdjunction.homEquiv _ _).symm ((adj.homEquiv _ _).symm (hE₀.preimage
      (g ≫ inv c))), ?_, fun h hh => ?_⟩
  · refine (claim _).trans ?_
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Functor.FullyFaithful.map_preimage,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  · apply (e.toAdjunction.homEquiv _ _).injective
    apply (adj.homEquiv _ _).injective
    apply hE₀.map_injective
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Functor.FullyFaithful.map_preimage]
    have hh' := (claim h).symm.trans hh
    rw [← hh', Category.assoc, IsIso.hom_inv_id, Category.comp_id]

include hE₀ in
/-- The same, for the unit followed by an isomorphism out of the image of the left adjoint. -/
theorem existsUnique_of_adjunction_iso (F : 𝒟') {G : 𝒞'} (γ : L.obj F ≅ G) (M : 𝒞)
    (g : E₀.obj F ⟶ R.obj M) :
    ∃! h : e.functor.obj G ⟶ M,
      (E₀.map (adj.unit.app F ≫ R'.map γ.hom) ≫ β.hom.app G) ≫ R.map h = g := by
  have key : ∀ h : e.functor.obj G ⟶ M,
      (E₀.map (adj.unit.app F ≫ R'.map γ.hom) ≫ β.hom.app G) ≫ R.map h =
        (E₀.map (adj.unit.app F) ≫ β.hom.app (L.obj F)) ≫ R.map (e.functor.map γ.hom ≫ h) := by
    intro h
    have hn := β.hom.naturality γ.hom
    simp only [Functor.comp_map] at hn
    rw [E₀.map_comp, R.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% hn]
  obtain ⟨h₀, hh₀, hu₀⟩ := existsUnique_of_adjunction adj e hE₀ R β F M g
  refine ⟨e.functor.map γ.inv ≫ h₀, ?_, fun h hh => ?_⟩
  · beta_reduce
    rw [key, ← Category.assoc, ← e.functor.map_comp, Iso.hom_inv_id, e.functor.map_id,
      Category.id_comp]
    exact hh₀
  · have := hu₀ _ ((key h).symm.trans hh)
    rw [← this, ← Category.assoc, ← e.functor.map_comp, Iso.inv_hom_id, e.functor.map_id,
      Category.id_comp]

end Transport

variable (D : InverseSystemOfFiniteSites.{v, u, w}) {t : D.I} (ht : IsTerminal t)

/-- The functor to a level from the terminal level factors through every transition. -/
theorem u_from_comp {i j : D.I} (a : j ⟶ i) :
    D.u (ht.from j) = D.u (ht.from i) ⋙ D.u a := by
  rw [← D.comp a (ht.from i), ht.hom_ext (a ≫ ht.from i) (ht.from j)]

/-- Precomposing a presheaf on the level `j` with the functor from the terminal level is the same
as precomposing first with the transition `a` and then with the functor to the level `i`. -/
theorem op_from_comp {i j : D.I} (a : j ⟶ i) {A : Type*} [Category A] (P : (D.C j)ᵒᵖ ⥤ A) :
    (D.u (ht.from j)).op ⋙ P = (D.u (ht.from i)).op ⋙ (D.u a).op ⋙ P := by
  rw [u_from_comp D ht a]
  rfl

/-- Moving a transport along an equality of objects past a component of a natural
transformation. -/
@[reassoc]
theorem eqToHom_comp_app {B : Type*} [Category B] {C' : Type*} [Category C'] {P Q : B ⥤ C'}
    (φ : P ⟶ Q) {X Y : B} (h : X = Y) (p : P.obj X = P.obj Y) :
    eqToHom p ≫ φ.app Y = φ.app X ≫ eqToHom (congrArg Q.obj h) := by
  subst h
  simp

variable {A : Type*} [Category A] {F₀ : Sheaf (D.J t) A} {F : ∀ i, Sheaf (D.J i) A}
  (ε : ∀ i, F₀.obj ⟶ (D.u (ht.from i)).op ⋙ (F i).obj)

/-- **The universal property of the inverse image** `Fᵢ = f_{!ᵢ}⁻¹F₀`: every map from `F₀` to the
direct image `u_{!ᵢ,*}M` of a sheaf `M` on the level `i` factors uniquely through `εᵢ`. -/
def IsUniversalArrow (i : D.I) : Prop :=
  ∀ (M : Sheaf (D.J i) A) (g : F₀.obj ⟶ (D.u (ht.from i)).op ⋙ M.obj),
    ∃! h : F i ⟶ M, ε i ≫ Functor.whiskerLeft (D.u (ht.from i)).op h.hom = g

variable {D ht ε} in
/-- Two maps out of a universal arrow agreeing after it are equal. -/
theorem IsUniversalArrow.hom_ext {i : D.I} (h : IsUniversalArrow D ht ε i) {M : Sheaf (D.J i) A}
    {f g : F i ⟶ M}
    (hfg : ε i ≫ Functor.whiskerLeft (D.u (ht.from i)).op f.hom =
      ε i ≫ Functor.whiskerLeft (D.u (ht.from i)).op g.hom) : f = g :=
  (h M _).unique rfl hfg.symm

variable (huniv : ∀ i, IsUniversalArrow D ht ε i)

/-- Two maps of presheaves out of a universal arrow agreeing after it are equal. -/
private theorem hom_ext_obj {i : D.I} (h : IsUniversalArrow D ht ε i)
    {P : (D.C i)ᵒᵖ ⥤ A} (hP : Presheaf.IsSheaf (D.J i) P) {f g : (F i).obj ⟶ P}
    (hfg : ε i ≫ Functor.whiskerLeft (D.u (ht.from i)).op f =
      ε i ≫ Functor.whiskerLeft (D.u (ht.from i)).op g) : f = g := by
  have := h.hom_ext (M := ⟨P, hP⟩) (f := ObjectProperty.homMk f)
    (g := ObjectProperty.homMk g) hfg
  exact congrArg (fun φ => φ.hom) this

/-- The direct image of a sheaf of a later level along a transition. -/
abbrev push {i j : D.I} (a : j ⟶ i) (M : Sheaf (D.J j) A) : Sheaf (D.J i) A :=
  letI := D.continuous a
  ((D.u a).sheafPushforwardContinuous A (D.J i) (D.J j)).obj M

/-- **The transition maps of the system of inverse images**, in adjoint form `Fᵢ ⟶ f_{a,*}F_j`:
the unique map carrying `εᵢ` to `ε_j`. -/
noncomputable def ψ {i j : D.I} (a : j ⟶ i) : (F i).obj ⟶ (D.u a).op ⋙ (F j).obj :=
  ((huniv i (push D a (F j)) (ε j ≫ eqToHom (op_from_comp D ht a (F j).obj))).exists.choose).hom

/-- The transition map `ψ a` carries `εᵢ` to `ε_j`, up to the equality `op_from_comp`. -/
theorem ψ_spec {i j : D.I} (a : j ⟶ i) :
    ε i ≫ Functor.whiskerLeft (D.u (ht.from i)).op (ψ D ht ε huniv a) =
      ε j ≫ eqToHom (op_from_comp D ht a (F j).obj) :=
  (huniv i (push D a (F j)) (ε j ≫ eqToHom (op_from_comp D ht a (F j).obj))).exists.choose_spec

/-- The two composite functors along a composite transition. -/
theorem op_comp_eq {i j k : D.I} (a : j ⟶ i) (b : k ⟶ j) (P : (D.C k)ᵒᵖ ⥤ A) :
    (D.u a).op ⋙ (D.u b).op ⋙ P = (D.u (b ≫ a)).op ⋙ P := by
  rw [D.comp b a]
  rfl

/-- A map `ψ a ≫ u_a^* χ ≫ eqToHom e` is carried by `εᵢ` to `ε_j ≫ χ`, up to `eqToHom`. -/
private theorem arrow_comp_ψ_whiskerLeft {i j : D.I} (a : j ⟶ i) {W : (D.C j)ᵒᵖ ⥤ A}
    {Q : (D.C i)ᵒᵖ ⥤ A} (χ : (F j).obj ⟶ W) (e : (D.u a).op ⋙ W = Q) :
    ε i ≫ Functor.whiskerLeft (D.u (ht.from i)).op
        (ψ D ht ε huniv a ≫ Functor.whiskerLeft (D.u a).op χ ≫ eqToHom e) =
      ε j ≫ Functor.whiskerLeft (D.u (ht.from j)).op χ ≫
        eqToHom ((op_from_comp D ht a W).trans (congrArg ((D.u (ht.from i)).op ⋙ ·) e)) := by
  subst e
  ext U
  have h1 := congrArg (fun φ => φ.app U) (ψ_spec D ht ε huniv a)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app, eqToHom_refl,
    Category.comp_id] at h1 ⊢
  have hX : (D.u (ht.from j)).op.obj U = (D.u a).op.obj ((D.u (ht.from i)).op.obj U) := by
    rw [u_from_comp D ht a]
    rfl
  rw [reassoc_of% h1, eqToHom_comp_app χ hX]

/-- **The cocycle condition of the system of inverse images**, as an identity of maps of
presheaves. -/
theorem ψ_comp {i j k : D.I} (a : j ⟶ i) (b : k ⟶ j) :
    ψ D ht ε huniv (b ≫ a) = ψ D ht ε huniv a ≫ Functor.whiskerLeft (D.u a).op (ψ D ht ε huniv b) ≫
      eqToHom (op_comp_eq D a b (F k).obj) := by
  refine hom_ext_obj D ht ε (huniv i) (P := (D.u (b ≫ a)).op ⋙ (F k).obj)
    (push D (b ≫ a) (F k)).property ?_
  rw [ψ_spec D ht ε huniv (b ≫ a), arrow_comp_ψ_whiskerLeft D ht ε huniv a,
    reassoc_of% ψ_spec D ht ε huniv b, eqToHom_trans]

/-! ### The colimit on a colimit site -/

section Colimit

variable {C : Type*} [Category C] (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (K : GrothendieckTopology C) [∀ i, (uC i).IsContinuous (D.J i) K]
  {G : Sheaf K A} (εG : F₀.obj ⟶ (uC t).op ⋙ G.obj)

include hu in
/-- Precomposing a presheaf on the colimit site with the functor from a level `j` and then with a
transition `a : j ⟶ i` is precomposing with the functor from the level `i`. -/
theorem op_uC_eq {i j : D.I} (a : j ⟶ i) (P : Cᵒᵖ ⥤ A) :
    (D.u a).op ⋙ (uC j).op ⋙ P = (uC i).op ⋙ P := by
  rw [← hu a]
  rfl

/-- The direct image of a sheaf on the colimit site to a level. -/
abbrev pushC (i : D.I) (M : Sheaf K A) : Sheaf (D.J i) A :=
  ((uC i).sheafPushforwardContinuous A (D.J i) K).obj M

/-- **The structure maps of the colimit** `f_t⁻¹F₀`, in adjoint form `Fᵢ ⟶ f_{i,*}G`: the unique
map carrying `εᵢ` to `ε_G`. -/
noncomputable def ι (i : D.I) : (F i).obj ⟶ (uC i).op ⋙ G.obj :=
  ((huniv i (pushC D uC K i G)
    (εG ≫ eqToHom (op_uC_eq D uC hu (ht.from i) G.obj).symm)).exists.choose).hom

/-- The structure map `ι i` carries `εᵢ` to `ε_G`, up to the equality `op_uC_eq`. -/
theorem ι_spec (i : D.I) :
    ε i ≫ Functor.whiskerLeft (D.u (ht.from i)).op (ι D ht ε huniv uC hu K εG i) =
      εG ≫ eqToHom (op_uC_eq D uC hu (ht.from i) G.obj).symm :=
  (huniv i (pushC D uC K i G)
    (εG ≫ eqToHom (op_uC_eq D uC hu (ht.from i) G.obj).symm)).exists.choose_spec

/-- The structure maps of the colimit are compatible with the transitions. -/
theorem ι_comp {i j : D.I} (a : j ⟶ i) :
    ι D ht ε huniv uC hu K εG i = ψ D ht ε huniv a ≫
      Functor.whiskerLeft (D.u a).op (ι D ht ε huniv uC hu K εG j) ≫
        eqToHom (op_uC_eq D uC hu a G.obj) := by
  refine hom_ext_obj D ht ε (huniv i) (P := (uC i).op ⋙ G.obj) (pushC D uC K i G).property ?_
  rw [ι_spec D ht ε huniv uC hu K εG i, arrow_comp_ψ_whiskerLeft D ht ε huniv a,
    reassoc_of% ι_spec D ht ε huniv uC hu K εG j, eqToHom_trans]

variable {D ht ε huniv uC hu K εG} in
/-- **The colimit property of `f_t⁻¹F₀`.** If `ε_G` is a universal arrow for the sheaves on the
colimit site, then every family of maps `Fᵢ ⟶ f_{i,*}H` compatible with the transitions factors
uniquely through the structure maps `ι`. -/
theorem existsUnique_of_compatible
    (hεG : ∀ (H : Sheaf K A) (g : F₀.obj ⟶ (uC t).op ⋙ H.obj),
      ∃! h : G ⟶ H, εG ≫ Functor.whiskerLeft (uC t).op h.hom = g)
    (H : Sheaf K A) (g : ∀ i, (F i).obj ⟶ (uC i).op ⋙ H.obj)
    (hg : ∀ {i j : D.I} (a : j ⟶ i), g i = ψ D ht ε huniv a ≫
      Functor.whiskerLeft (D.u a).op (g j) ≫ eqToHom (op_uC_eq D uC hu a H.obj)) :
    ∃! h : G ⟶ H, ∀ i, ι D ht ε huniv uC hu K εG i ≫ Functor.whiskerLeft (uC i).op h.hom = g i := by
  obtain ⟨h, hh, -⟩ := hεG H (ε t ≫ Functor.whiskerLeft (D.u (ht.from t)).op (g t) ≫
    eqToHom (op_uC_eq D uC hu (ht.from t) H.obj))
  have hforce : ∀ (h' : G ⟶ H), (∀ i, ι D ht ε huniv uC hu K εG i ≫
      Functor.whiskerLeft (uC i).op h'.hom = g i) →
      εG ≫ Functor.whiskerLeft (uC t).op h'.hom = ε t ≫
        Functor.whiskerLeft (D.u (ht.from t)).op (g t) ≫
          eqToHom (op_uC_eq D uC hu (ht.from t) H.obj) := by
    intro h' hh'
    rw [← hh' t]
    ext U
    have h1 := congrArg (fun φ => φ.app U) (ι_spec D ht ε huniv uC hu K εG t)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app] at h1 ⊢
    have hX : (uC t).op.obj U = (uC t).op.obj ((D.u (ht.from t)).op.obj U) :=
      congrArg op (Functor.congr_obj (hu (ht.from t)) U.unop).symm
    rw [Category.assoc, reassoc_of% h1, eqToHom_comp_app_assoc h'.hom hX, eqToHom_trans,
      eqToHom_refl, Category.comp_id]
  refine ⟨h, fun i => ?_, fun h' hh' => (hεG H _).unique (hforce h' hh') hh⟩
  refine hom_ext_obj D ht ε (huniv i) (P := (uC i).op ⋙ H.obj) (pushC D uC K i H).property ?_
  ext U
  have h1 := congrArg (fun φ => φ.app U) (ι_spec D ht ε huniv uC hu K εG i)
  have h2 := congrArg (fun φ => φ.app U) hh
  have h3 := congrArg (fun φ => φ.app U) (ψ_spec D ht ε huniv (ht.from i))
  have h4 := congrArg (fun φ => φ.app ((D.u (ht.from t)).op.obj U)) (hg (ht.from i))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app] at h1 h2 h3 h4 ⊢
  have hX1 : (uC t).op.obj U = (uC i).op.obj ((D.u (ht.from i)).op.obj U) :=
    congrArg op (Functor.congr_obj (hu (ht.from i)) U.unop).symm
  have hX2 : (D.u (ht.from i)).op.obj U =
      (D.u (ht.from i)).op.obj ((D.u (ht.from t)).op.obj U) := by
    rw [ht.hom_ext (ht.from t) (𝟙 t), D.id_map]
    rfl
  rw [reassoc_of% h1, eqToHom_comp_app h.hom hX1, reassoc_of% h2, h4]
  simp only [Category.assoc]
  rw [reassoc_of% h3, eqToHom_comp_app_assoc (g i) hX2]
  simp

end Colimit

/-! ### The abelian system and its colimit presentation -/

section Abelian

open InverseSystemOfFiniteSites Stacks.WeakSites.ColimitSiteCohomology

variable {D ht} {F₀' : Sheaf (D.J t) Ab.{max u v w}} {F' : ∀ i, Sheaf (D.J i) Ab.{max u v w}}
  {ε' : ∀ i, F₀'.obj ⟶ (D.u (ht.from i)).op ⋙ (F' i).obj}
  (huniv' : ∀ i, IsUniversalArrow D ht ε' i)

/-- The transition maps as maps of sheaves into the direct image. -/
noncomputable def ψSheaf {i j : D.I} (a : j ⟶ i) :
    F' i ⟶ (abelianSheafPushforward.{v, u, w, w} D a).obj (F' j) :=
  ObjectProperty.homMk (ψ D ht ε' huniv' a)

omit [∀ i, IsUniversalArrow D ht ε' i] in
/-- The components of the isomorphism between the direct image along an identity transition and
the identity are the restriction maps along the equality of objects. -/
theorem pushforwardIdIso_hom_app_app (i : D.I) (X : Sheaf (D.J i) Ab.{max u v w}) (U : D.C i) :
    (((abelianSheafPushforwardIdIso.{v, u, w, w} D i).hom.app X).hom.app (op U)) =
      X.obj.map (eqToHom (congrArg op (Functor.congr_obj (D.id_map i).symm U))) := by
  dsimp [abelianSheafPushforwardIdIso, abelianSheafPushforward]
  simp only [Functor.sheafPushforwardContinuousId, Iso.refl_inv, NatTrans.id_app,
    ObjectProperty.FullSubcategory.id_hom, Functor.sheafPushforwardContinuousIso_inv, eqToIso.hom,
    Functor.sheafPushforwardContinuousNatTrans_app_hom, ObjectProperty.ι_obj,
    Functor.whiskerRight_app, Functor.op_obj, Functor.id_obj, NatTrans.op_app, eqToHom_app,
    eqToHom_op]
  exact Category.id_comp _

/-- The components of the isomorphism between the direct image along a composite transition and
the composite of the direct images are the restriction maps along the equality of objects. -/
theorem pushforwardCompIso_hom_app_app {i j k : D.I} (a : j ⟶ i) (b : k ⟶ j)
    (X : Sheaf (D.J k) Ab.{max u v w}) (U : D.C i) :
    (((abelianSheafPushforwardCompIso.{v, u, w, w} D b a).hom.app X).hom.app (op U)) =
      X.obj.map (eqToHom (congrArg op (Functor.congr_obj (D.comp b a).symm U))) := by
  let _ := D.continuous a
  let _ := D.continuous b
  let _ := D.continuous (b ≫ a)
  dsimp [abelianSheafPushforwardCompIso, abelianSheafPushforward]
  exact sheafPushforwardContinuousComp'_hom_app_app.{w, max u v w} (D.comp b a).symm
    (D.J i) (D.J j) (D.J k) X U

/-- The transition map along an identity is the isomorphism between the direct image along the
identity and the identity. -/
theorem ψSheaf_id (i : D.I) :
    ψSheaf huniv' (𝟙 i) = (abelianSheafPushforwardIdIso.{v, u, w, w} D i).hom.app (F' i) := by
  apply (huniv' i).hom_ext (M := push D (𝟙 i) (F' i))
  change ε' i ≫ Functor.whiskerLeft (D.u (ht.from i)).op (ψ D ht ε' huniv' (𝟙 i)) = _
  rw [ψ_spec D ht ε' huniv' (𝟙 i)]
  refine NatTrans.ext (funext fun U => ?_)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app]
  exact congrArg ((ε' i).app U ≫ ·)
    ((eqToHom_map (F' i).obj _).symm.trans (pushforwardIdIso_hom_app_app i (F' i) _).symm)

/-- The transition map along a composite is the composite of the transition maps, followed by the
isomorphism of direct images along the composite. -/
theorem ψSheaf_comp {i j k : D.I} (a : j ⟶ i) (b : k ⟶ j) :
    ψSheaf huniv' (b ≫ a) = ψSheaf huniv' a ≫
      (abelianSheafPushforward.{v, u, w, w} D a).map (ψSheaf huniv' b) ≫
        (abelianSheafPushforwardCompIso.{v, u, w, w} D b a).hom.app (F' k) := by
  apply Sheaf.hom_ext
  refine (ψ_comp D ht ε' huniv' a b).trans ?_
  congr 2
  refine NatTrans.ext (funext fun U => ?_)
  rw [eqToHom_app, pushforwardCompIso_hom_app_app, eqToHom_map]

/-- **The system of inverse images, as a system of abelian sheaves of Stacks 0EXZ**: the
transition `f_a⁻¹Fᵢ ⟶ F_j` is the adjoint of `ψ_a`. -/
noncomputable def abelianSystem : AbelianSheafSystem.{v, u, w, w} D where
  obj := F'
  map a := (abelianSheafAdjunction.{v, u, w, w} D a).homEquiv _ _ |>.symm <| ψSheaf huniv' a
  map_id i := by
    have hh : (abelianSheafAdjunction.{v, u, w, w} D (𝟙 i)).homEquiv (F' i) (F' i)
        ((abelianSheafPullbackIdIso.{v, u, w, w} D i).hom.app (F' i)) = ψSheaf huniv' (𝟙 i) := by
      rw [ψSheaf_id]
      exact Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ _
    rw [← hh]
    simpa only [Equiv.symm_apply_apply, Functor.id_obj] using
      (abelianSheafPullbackIdIso.{v, u, w, w} D i).inv_hom_id_app (F' i)
  map_comp {i j k} a b := by
    apply (abelianSheafAdjunction.{v, u, w, w} D (a ≫ b)).homEquiv _ _ |>.injective
    dsimp only [abelianSheafPullbackCompIso]
    have hinv : ∀ {A B : Type _} [Category A] [Category B] {L L' : A ⥤ B} {R : B ⥤ A}
        (a : L ⊣ R) (b : L' ⊣ R) {X : A} {Y : B} (f : L.obj X ⟶ Y),
        b.homEquiv X Y ((a.leftAdjointUniq b).inv.app X ≫ f) = a.homEquiv X Y f := by
      intro A B _ _ L L' R a b X Y f
      rw [Adjunction.leftAdjointUniq_inv_app, b.homEquiv_naturality_right,
        Adjunction.homEquiv_leftAdjointUniq_hom_app]
      rfl
    rw [hinv, Adjunction.homEquiv_ofNatIsoRight_apply,
      Adjunction.comp_homEquiv]
    change ((abelianSheafAdjunction.{v, u, w, w} D b).homEquiv _ _)
      (((abelianSheafAdjunction.{v, u, w, w} D a).homEquiv _ _)
        ((abelianSheafPullback.{v, u, w, w} D a).map
          (((abelianSheafAdjunction.{v, u, w, w} D b).homEquiv _ _).symm (ψSheaf huniv' b)) ≫
          ((abelianSheafAdjunction.{v, u, w, w} D a).homEquiv _ _).symm (ψSheaf huniv' a))) ≫
        (abelianSheafPushforwardCompIso.{v, u, w, w} D a b).hom.app (F' i) = _
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
      Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
    exact (ψSheaf_comp huniv' b a).symm

/-- The transition of `abelianSystem` along `a`, in adjoint form, is `ψ a`. -/
theorem transition_abelianSystem {i j : D.I} (a : j ⟶ i) :
    transition D (abelianSystem huniv') a = ψ D ht ε' huniv' a := by
  unfold transition abelianSystem
  rw [Equiv.apply_symm_apply]
  rfl

variable {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (K : Precoverage C) [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]
  {G : Sheaf K.toGrothendieck Ab.{max u v w}} (εG : F₀'.obj ⟶ (uC t).op ⋙ G.obj)

/-- **The colimit presentation of Stacks 09YP for the system of inverse images**: if `ε_G` is a
universal arrow for the sheaves on the colimit site, then `G` with the structure maps `ι` presents
`colim f_i⁻¹ Fᵢ`. -/
theorem isColimitPresentation_abelianSystem
    (hεG : ∀ (H : Sheaf K.toGrothendieck Ab.{max u v w}) (g : F₀'.obj ⟶ (uC t).op ⋙ H.obj),
      ∃! h : G ⟶ H, εG ≫ Functor.whiskerLeft (uC t).op h.hom = g) :
    IsColimitPresentation.{v, u, w, w} D uC hu K (abelianSystem huniv') G
      (ι D ht ε' huniv' uC hu K.toGrothendieck εG) := by
  refine ⟨fun {j k} a => ?_, fun H g hg => ?_⟩
  · rw [transition_abelianSystem]
    exact ι_comp D ht ε' huniv' uC hu K.toGrothendieck εG a
  · refine existsUnique_of_compatible hεG H g (fun {i j} a => ?_)
    have := hg a
    rw [transition_abelianSystem] at this
    exact this

end Abelian

end Stacks.WeakSites.PullbackSystem
