module

import all StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSitesSystems

/-!
# Systems of abelian sheaves from transition data satisfying only the cocycle law

`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.AbelianSheafSystem` — the notion of
coefficients the colimit statements of [Stacks, Tag 09YP] and [Stacks, Tag 09YQ] take on the levels
of [Stacks, Tag 0EYL] — carries a `map_id` field, which says that the transition along an identity
arrow is the canonical transport and in particular invertible
(`Stacks.WeakSites.ColimitSiteCohomology.isIso_transition_id`). The source of a system of sheaves
on an inverse system of *schemes*, [Stacks, Tag 0EZL], imposes no such condition: it asks for the
cocycle law alone, and `Stacks.EtaleCohomology.EtaleSheafSystem` follows it. So transition data
arising from geometry is a system in the weaker sense only, and
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimitPresentation_zeroTransitionSystem`
exhibits such data, carrying a colimit presentation, whose identity transition is zero on a nonzero
sheaf. A levelwise transport of it into an `AbelianSheafSystem` therefore does not exist.

This file closes that gap. The transition datum at an identity arrow of weaker data is an
**idempotent** endomorphism of the sheaf at the level; the sheaf categories of the levels are
abelian, hence idempotent complete; and splitting those idempotents produces an honest
`AbelianSheafSystem` which a compatible family — indeed a whole colimit presentation — for the
original data is a compatible family, respectively a colimit presentation, for.

The reason the construction is available here and not on Mathlib's small étale sites is that
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites` carries `id_map` and `comp` as
*equalities* of functors. Every comparison between transition functors is then a
`CategoryTheory.eqToHom`, so the unit and associativity coherences the splitting argument needs
hold by proof irrelevance; on the small étale sites base change along `𝟙 X` is `U ↦ U ×_X X`
rather than the identity functor and no such equality is available.

## Main definitions

* `CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.AbelianCocycleSystem` — **abelian
  sheaves on the levels together with direct-image transition data satisfying only the cocycle
  law.** This is the abelian counterpart of
  `CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.SheafSystem`, and the shape
  [Stacks, Tag 0EZL] imposes.
* `...AbelianCocycleSystem.idem` — the transition at an identity arrow, read as an endomorphism of
  the sheaf at the level through the strictness field `id_map`.
* `...AbelianCocycleSystem.Splitting` — a splitting of that idempotent at one level.
* `...AbelianCocycleSystem.toAbelianSheafSystem` — the passage from direct-image transition data
  that *does* satisfy the identity law to an `AbelianSheafSystem`.
* `...AbelianSheafSystem.toAbelianCocycleSystem` — and the passage back: a system of abelian
  sheaves *is* such data, by its own cocycle law.
* `...AbelianCocycleSystem.split` — **the system of abelian sheaves obtained by splitting the
  identity arrows' idempotents.**
* `...AbelianCocycleSystem.IsCompatible` and `...AbelianCocycleSystem.IsColimitPresentation` — the
  compatibility and colimit-presentation predicates of
  `Stacks.WeakSites.ColimitSiteCohomology`, read off data that satisfies only the cocycle law.

## Main results

* `...AbelianCocycleSystem.idem_idem` — **the identity transition of cocycle data is
  idempotent.**
* `...AbelianCocycleSystem.idem_comp_map` — and it acts as the identity on every transition.
* `...AbelianCocycleSystem.nonempty_splitting` — a splitting exists at every level, the sheaf
  category of a level being abelian.
* `...AbelianCocycleSystem.splitCocycle_map_id` — the split transition data satisfies the identity
  law, so `split` is defined.
* `Stacks.WeakSites.ColimitSiteCohomology.isCompatible_split` — **a compatible family for the
  unsplit data is a compatible family for the split system**, restricted along the inclusions of
  the splittings.
* `...AbelianCocycleSystem.isColimitPresentation_split` — **and a colimit presentation for the
  unsplit data is a colimit presentation for the split system**, same sheaf on the colimit site,
  legs restricted along the inclusions. So a crossing that produces cocycle data on the levels
  together with a presentation of it owes nothing further on the coefficient side.
* `...AbelianSheafSystem.idem_toAbelianCocycleSystem` — the idempotent of a system that already
  satisfies the identity law is the identity, so the splitting is vacuous there: the construction
  is a generalisation and not a modification.

## Implementation notes

The transition data is carried in the direct-image (presheaf) form `F_j ⟶ u_a^{op} ⋙ F_i`, the
form `Stacks.WeakSites.ColimitSiteCohomology.transition` reads an `AbelianSheafSystem` in, rather
than as a morphism `f_a^{-1}F_j ⟶ F_i` of sheaves. That is what makes the coherences free: in the
direct-image form the comparison of `u_{a ≫ b}` with `u_b ⋙ u_a` and of `u_{𝟙 i}` with the
identity are `eqToHom`s of functor equalities, so a composite of them between a type and itself is
the identity by proof irrelevance alone, whereas in the inverse-image form they are the
uniqueness isomorphisms of left adjoints and their unit coherence is a theorem this library does
not have. `toAbelianSheafSystem` crosses between the two forms once, through the adjunction
bijection, and is the only place the comparison isomorphisms of direct images are evaluated.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w t

namespace Stacks.WeakSites.ColimitSiteCohomology

/-- **Transport of restriction along an identification of two functors is natural.** If `G = G'`
then the `CategoryTheory.eqToHom` identifying `G^{op} ⋙ P` with `G'^{op} ⋙ P` commutes with
restriction of a morphism of presheaves along `G`. -/
@[reassoc]
theorem eqToHom_comp_whiskerLeft_op {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    {A : Type*} [Category* A] {G G' : C₁ ⥤ C₂} (hG : G = G') {P Q : C₂ᵒᵖ ⥤ A} (α : P ⟶ Q) :
    eqToHom (congrArg (fun H : C₁ ⥤ C₂ => H.op ⋙ P) hG) ≫ Functor.whiskerLeft G'.op α =
      Functor.whiskerLeft G.op α ≫ eqToHom (congrArg (fun H : C₁ ⥤ C₂ => H.op ⋙ Q) hG) := by
  subst hG
  ext U
  simp

/-- **Transport along an identification of a composite of functors is natural**, the composite
being read as two successive restrictions on the right-hand side. This is the form in which the
cocycle law of direct-image transition data is used. -/
@[reassoc]
theorem eqToHom_comp_whiskerLeft_op_comp {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] {A : Type*} [Category* A] {G : C₁ ⥤ C₂} {G' : C₂ ⥤ C₃} {G'' : C₁ ⥤ C₃}
    (hG : G ⋙ G' = G'') {P Q : C₃ᵒᵖ ⥤ A} (α : P ⟶ Q) :
    eqToHom (congrArg (fun H : C₁ ⥤ C₃ => H.op ⋙ P) hG) ≫ Functor.whiskerLeft G''.op α =
      Functor.whiskerLeft G.op (Functor.whiskerLeft G'.op α) ≫
        eqToHom (congrArg (fun H : C₁ ⥤ C₃ => H.op ⋙ Q) hG) := by
  subst hG
  ext U
  simp

/-- **Transport along an identification of a functor with the identity is natural.** The special
case of `eqToHom_comp_whiskerLeft_op` in which one side is the identity functor, so that
restriction along it disappears. -/
@[reassoc]
theorem eqToHom_id_comp_whiskerLeft_op {C₁ : Type*} [Category* C₁] {A : Type*} [Category* A]
    {G : C₁ ⥤ C₁} (hG : G = 𝟭 C₁) {P Q : C₁ᵒᵖ ⥤ A} (α : P ⟶ Q) :
    eqToHom (congrArg (fun H : C₁ ⥤ C₁ => H.op ⋙ P) hG.symm) ≫ Functor.whiskerLeft G.op α =
      α ≫ eqToHom (congrArg (fun H : C₁ ⥤ C₁ => H.op ⋙ Q) hG.symm) := by
  subst hG
  ext U
  simp

end Stacks.WeakSites.ColimitSiteCohomology

namespace InverseSystemOfFiniteSites

/-! ### The comparison isomorphisms of direct images, as transports -/

/-- **The composition comparison of direct images is the transport along `comp`**, read as a
morphism of presheaves: the inverse of
`InverseSystemOfFiniteSites.abelianSheafPushforwardCompIso` is the `CategoryTheory.eqToHom` of the
functor equality `u_{a ≫ b} = u_b ⋙ u_a`. -/
theorem pushforwardCompIso_inv_app_hom (D : InverseSystemOfFiniteSites.{v, u, w})
    {i j k : D.I} (a : i ⟶ j) (b : j ⟶ k) (X : Sheaf (D.J i) (Ab.{max u v w t})) :
    ((abelianSheafPushforwardCompIso.{v, u, w, t} D a b).inv.app X).hom =
      eqToHom (congrArg (fun H : D.C k ⥤ D.C i => H.op ⋙ X.obj) (D.comp a b)) := by
  refine NatTrans.ext (funext fun U => ?_)
  obtain ⟨U⟩ := U
  rw [pushforwardCompIso_inv_app_app.{v, u, w, t} D a b X U, eqToHom_map, eqToHom_app]

/-- **The identity comparison of direct images is the transport along `id_map`**, read as a
morphism of presheaves: `InverseSystemOfFiniteSites.abelianSheafPushforwardIdIso` is the
`CategoryTheory.eqToHom` of the functor equality `𝟭 = u_{𝟙 i}`. -/
theorem pushforwardIdIso_hom_app_hom (D : InverseSystemOfFiniteSites.{v, u, w}) (i : D.I)
    (X : Sheaf (D.J i) (Ab.{max u v w t})) :
    ((abelianSheafPushforwardIdIso.{v, u, w, t} D i).hom.app X).hom =
      eqToHom (congrArg (fun H : D.C i ⥤ D.C i => H.op ⋙ X.obj) (D.id_map i).symm) := by
  refine NatTrans.ext (funext fun U => ?_)
  obtain ⟨U⟩ := U
  rw [pushforwardIdIso_hom_app_app.{v, u, w, t} D i X U, eqToHom_map, eqToHom_app]

/-! ### Transition data satisfying only the cocycle law -/

/-- **Abelian sheaves on the levels of an inverse system of sites with finite coverings, together
with direct-image transition data satisfying only the cocycle law.**

This is `InverseSystemOfFiniteSites.AbelianSheafSystem` with the identity law dropped and the
transitions carried in the direct-image form, so it is the abelian counterpart of
`InverseSystemOfFiniteSites.SheafSystem` and the exact shape the source of [Stacks, Tag 0EZL]
imposes: the compatibility it asks for is the cocycle condition, and nothing is asked of the datum
at an identity arrow. `InverseSystemOfFiniteSites.AbelianCocycleSystem.split` turns such data into
a genuine `AbelianSheafSystem` by splitting the identity arrows' idempotents. -/
structure AbelianCocycleSystem (D : InverseSystemOfFiniteSites.{v, u, w}) where
  /-- The abelian sheaf at an index. -/
  obj : ∀ i, Sheaf (D.J i) (Ab.{max u v w t})
  /-- The direct-image transition morphism, on underlying presheaves. -/
  map : ∀ {i j : D.I} (a : i ⟶ j), (obj j).obj ⟶ (D.u a).op ⋙ (obj i).obj
  /-- The cocycle law: the transition along a composite is the composite of the transitions, up to
  the identification of `u_{a ≫ b}` with `u_b ⋙ u_a` recorded by the system. -/
  map_comp : ∀ {i j k : D.I} (a : i ⟶ j) (b : j ⟶ k),
    map (a ≫ b) = (map b ≫ Functor.whiskerLeft (D.u b).op (map a)) ≫
      eqToHom (congrArg (fun H : D.C k ⥤ D.C i => H.op ⋙ (obj i).obj) (D.comp a b).symm)

namespace AbelianCocycleSystem

variable {D : InverseSystemOfFiniteSites.{v, u, w}} (M : AbelianCocycleSystem.{v, u, w, t} D)

/-- **The transition at an identity arrow, as an endomorphism of the sheaf at the level.** The
transition functor of an identity arrow *is* the identity functor, by the strictness field
`InverseSystemOfFiniteSites.id_map`, so the datum `F_i ⟶ u_{𝟙 i}^{op} ⋙ F_i` becomes an
endomorphism of `F_i` once composed with the transport along that equality.

For an `InverseSystemOfFiniteSites.AbelianSheafSystem` this endomorphism is the identity — that is
the content of the `map_id` field, by
`Stacks.WeakSites.ColimitSiteCohomology.transition_id_eqToHom`. For cocycle data it is only
idempotent, `AbelianCocycleSystem.idem_idem`. -/
def idem (i : D.I) : M.obj i ⟶ M.obj i :=
  Sheaf.Hom.mk (M.map (𝟙 i) ≫
    eqToHom (congrArg (fun H : D.C i ⥤ D.C i => H.op ⋙ (M.obj i).obj) (D.id_map i)))

/-- The underlying morphism of `AbelianCocycleSystem.idem`. -/
theorem idem_hom (i : D.I) :
    (M.idem i).hom = M.map (𝟙 i) ≫
      eqToHom (congrArg (fun H : D.C i ⥤ D.C i => H.op ⋙ (M.obj i).obj) (D.id_map i)) :=
  rfl

/-- The transition at an identity arrow, recovered from `AbelianCocycleSystem.idem`. -/
theorem map_id_eq (i : D.I) :
    M.map (𝟙 i) = (M.idem i).hom ≫
      eqToHom (congrArg (fun H : D.C i ⥤ D.C i => H.op ⋙ (M.obj i).obj) (D.id_map i).symm) := by
  rw [idem_hom, Category.assoc]
  simp

/-- The cocycle law at an arrow presented as a composite. This is the `map_comp` field with the
composite generalised, which is what lets it be used at `a ≫ 𝟙 j = a`. -/
theorem map_comp' {i j k : D.I} (a : i ⟶ j) (b : j ⟶ k) {c : i ⟶ k} (hc : a ≫ b = c) :
    M.map c = (M.map b ≫ Functor.whiskerLeft (D.u b).op (M.map a)) ≫
      eqToHom (congrArg (fun H : D.C k ⥤ D.C i => H.op ⋙ (M.obj i).obj)
        ((D.comp a b).symm.trans (congrArg (fun e : i ⟶ k => D.u e) hc))) := by
  subst hc
  exact M.map_comp a b

/-- A morphism out of the sheaf at a level that is its own restriction along the identity
transition is fixed by the idempotent `AbelianCocycleSystem.idem`. -/
private theorem idem_comp_eq_self {k : D.I} {T : (D.C k)ᵒᵖ ⥤ Ab.{max u v w t}}
    (g : (M.obj k).obj ⟶ T) {e : (D.u (𝟙 k)).op ⋙ T = T}
    (h : g = M.map (𝟙 k) ≫ Functor.whiskerLeft (D.u (𝟙 k)).op g ≫ eqToHom e) :
    (M.idem k).hom ≫ g = g := by
  rw [M.map_id_eq k] at h
  simp only [Category.assoc] at h
  rw [Stacks.WeakSites.ColimitSiteCohomology.eqToHom_id_comp_whiskerLeft_op_assoc
    (D.id_map k) g] at h
  simp only [eqToHom_trans, eqToHom_refl, Category.comp_id] at h
  exact h.symm

/-- **The identity transition acts as the identity on every transition.** The cocycle law at
`a ≫ 𝟙 j = a`, with the transports cancelled. -/
theorem idem_comp_map {i j : D.I} (a : i ⟶ j) : (M.idem j).hom ≫ M.map a = M.map a :=
  M.idem_comp_eq_self _
    (by simpa only [Category.assoc] using M.map_comp' a (𝟙 j) (Category.comp_id a))

/-- **The identity transition of cocycle data is idempotent.** It is the identity only when the
data satisfies the identity law of an `InverseSystemOfFiniteSites.AbelianSheafSystem`; splitting
this idempotent is what `AbelianCocycleSystem.split` does. -/
theorem idem_idem (i : D.I) : M.idem i ≫ M.idem i = M.idem i := by
  refine Sheaf.hom_ext ?_
  calc (M.idem i ≫ M.idem i).hom
      = (M.idem i).hom ≫ M.map (𝟙 i) ≫
          eqToHom (congrArg (fun H : D.C i ⥤ D.C i => H.op ⋙ (M.obj i).obj) (D.id_map i)) := rfl
    _ = M.map (𝟙 i) ≫
          eqToHom (congrArg (fun H : D.C i ⥤ D.C i => H.op ⋙ (M.obj i).obj) (D.id_map i)) := by
        rw [← Category.assoc, M.idem_comp_map (𝟙 i)]
    _ = (M.idem i).hom := rfl

/-! ### Splitting the identity arrows' idempotents -/

/-- **A splitting of the idempotent `AbelianCocycleSystem.idem` at one level**: a sheaf there
together with an inclusion into and a projection from the sheaf of the data, composing to the
identity one way and to the idempotent the other. -/
structure Splitting (i : D.I) where
  /-- The split sheaf. -/
  obj : Sheaf (D.J i) (Ab.{max u v w t})
  /-- The inclusion of the split sheaf. -/
  incl : obj ⟶ M.obj i
  /-- The projection onto the split sheaf. -/
  proj : M.obj i ⟶ obj
  /-- The projection is a retraction of the inclusion. -/
  incl_proj : incl ≫ proj = 𝟙 obj
  /-- The other composite is the idempotent being split. -/
  proj_incl : proj ≫ incl = M.idem i

/-- The projection-inclusion composite of a splitting, on underlying presheaves. -/
private theorem proj_incl_hom {i : D.I} (S : M.Splitting i) :
    S.proj.hom ≫ S.incl.hom = (M.idem i).hom :=
  congrArg (fun f : M.obj i ⟶ M.obj i => f.hom) S.proj_incl

/-- The inclusion-projection composite of a splitting, on underlying presheaves. -/
private theorem incl_proj_hom {i : D.I} (S : M.Splitting i) :
    S.incl.hom ≫ S.proj.hom = 𝟙 S.obj.obj :=
  congrArg (fun f : S.obj ⟶ S.obj => f.hom) S.incl_proj

/-- **The idempotent of cocycle data splits at every level.** Abelian sheaves on the site of a
level form an abelian, hence idempotent complete, category. -/
theorem nonempty_splitting (i : D.I) : Nonempty (M.Splitting i) := by
  have := hasSheafifyAb.{v, u, w, t} D i
  obtain ⟨B, s, p, hsp, hps⟩ :=
    IsIdempotentComplete.idempotents_split (M.obj i) (M.idem i) (M.idem_idem i)
  exact ⟨B, s, p, hsp, hps⟩

/-- A chosen splitting of the idempotent at each level. -/
def splitting (i : D.I) : M.Splitting i := (M.nonempty_splitting i).some

/-- **The transition data of the split system**: the transition of the given data, pushed through
the inclusion of the splitting at the source and the projection of the splitting at the target.

That this satisfies the cocycle law uses `AbelianCocycleSystem.idem_comp_map`, the two
projection-inclusion composites of the splittings appearing exactly where the idempotent does.
That it satisfies the identity law as well is `AbelianCocycleSystem.splitCocycle_map_id`. -/
def splitCocycle (S : ∀ i, M.Splitting i) : AbelianCocycleSystem.{v, u, w, t} D where
  obj i := (S i).obj
  map {i j} a := (S j).incl.hom ≫ M.map a ≫ Functor.whiskerLeft (D.u a).op (S i).proj.hom
  map_comp {i j k} a b := by
    have hps : (S j).proj.hom ≫ (S j).incl.hom = (M.idem j).hom :=
      congrArg (fun f : M.obj j ⟶ M.obj j => f.hom) (S j).proj_incl
    rw [M.map_comp a b]
    simp only [Category.assoc]
    rw [Stacks.WeakSites.ColimitSiteCohomology.eqToHom_comp_whiskerLeft_op_comp
      (D.comp a b).symm (S i).proj.hom]
    simp only [Functor.whiskerLeft_comp, Category.assoc]
    conv_rhs =>
      rw [← Functor.whiskerLeft_comp_assoc, hps, ← Functor.whiskerLeft_comp_assoc,
        M.idem_comp_map a]

/-- The transition of `AbelianCocycleSystem.splitCocycle` at an arrow `a : i ⟶ j`. -/
theorem splitCocycle_map (S : ∀ i, M.Splitting i) {i j : D.I} (a : i ⟶ j) :
    (M.splitCocycle S).map a =
      (S j).incl.hom ≫ M.map a ≫ Functor.whiskerLeft (D.u a).op (S i).proj.hom :=
  rfl

/-- **The split transition data satisfies the identity law**: its datum at an identity arrow is the
canonical transport. The idempotent has become the identity, the splitting's two composites
replacing it by `incl ≫ proj = 𝟙`. -/
theorem splitCocycle_map_id (S : ∀ i, M.Splitting i) (i : D.I) :
    (M.splitCocycle S).map (𝟙 i) =
      eqToHom (congrArg (fun H : D.C i ⥤ D.C i => H.op ⋙ ((S i).obj).obj)
        (D.id_map i).symm) := by
  have hsp := M.incl_proj_hom (S i)
  have hi : (S i).incl.hom ≫ (M.idem i).hom = (S i).incl.hom := by
    rw [← M.proj_incl_hom (S i), ← Category.assoc, hsp, Category.id_comp]
  show (S i).incl.hom ≫ M.map (𝟙 i) ≫
      Functor.whiskerLeft (D.u (𝟙 i)).op (S i).proj.hom =
    eqToHom (congrArg (fun H : D.C i ⥤ D.C i => H.op ⋙ ((S i).obj).obj) (D.id_map i).symm)
  rw [M.map_id_eq i]
  simp only [Category.assoc]
  rw [Stacks.WeakSites.ColimitSiteCohomology.eqToHom_id_comp_whiskerLeft_op
    (D.id_map i) (S i).proj.hom, ← Category.assoc, hi, ← Category.assoc, hsp,
    Category.id_comp]

/-! ### From transition data with an identity law to a system of abelian sheaves -/

/-- **Direct-image transition data satisfying the identity law is a system of abelian sheaves.**
The transition is carried across the adjunction between inverse and direct image, and the two
fields of `InverseSystemOfFiniteSites.AbelianSheafSystem` become the two hypotheses here through
the comparison isomorphisms of direct images, evaluated by
`InverseSystemOfFiniteSites.pushforwardIdIso_hom_app_hom` and
`InverseSystemOfFiniteSites.pushforwardCompIso_inv_app_hom`. -/
def toAbelianSheafSystem
    (hid : ∀ i, M.map (𝟙 i) =
      eqToHom (congrArg (fun H : D.C i ⥤ D.C i => H.op ⋙ (M.obj i).obj) (D.id_map i).symm)) :
    AbelianSheafSystem.{v, u, w, t} D where
  obj := M.obj
  map {i j} a :=
    ((abelianSheafAdjunction.{v, u, w, t} D a).homEquiv (M.obj j) (M.obj i)).symm
      (Sheaf.Hom.mk (M.map a))
  map_id i := by
    have hunit := Adjunction.homEquiv_leftAdjointUniq_hom_app
      (abelianSheafAdjunction.{v, u, w, t} D (𝟙 i))
      (Adjunction.id.ofNatIsoRight (abelianSheafPushforwardIdIso.{v, u, w, t} D i)) (M.obj i)
    have h2 : (Adjunction.id.ofNatIsoRight
          (abelianSheafPushforwardIdIso.{v, u, w, t} D i)).unit.app (M.obj i) =
        (abelianSheafPushforwardIdIso.{v, u, w, t} D i).hom.app (M.obj i) := by
      simp [Adjunction.ofNatIsoRight]
    have h1 : ((abelianSheafAdjunction.{v, u, w, t} D (𝟙 i)).homEquiv
          (M.obj i) (M.obj i)).symm (Sheaf.Hom.mk (M.map (𝟙 i))) =
        (abelianSheafPullbackIdIso.{v, u, w, t} D i).hom.app (M.obj i) := by
      refine ((abelianSheafAdjunction.{v, u, w, t} D (𝟙 i)).homEquiv _ _).injective ?_
      rw [Equiv.apply_symm_apply]
      refine Eq.trans ?_ (hunit.trans h2).symm
      refine Sheaf.hom_ext ?_
      rw [pushforwardIdIso_hom_app_hom.{v, u, w, t} D i (M.obj i)]
      exact hid i
    rw [h1, Iso.inv_hom_id_app]
    rfl
  map_comp {i j k} a b := by
    have key := leftAdjointUniq_ofNatIsoRight_homEquiv_inv
      (abelianSheafAdjunction.{v, u, w, t} D b) (abelianSheafAdjunction.{v, u, w, t} D a)
      (abelianSheafAdjunction.{v, u, w, t} D (a ≫ b))
      (abelianSheafPushforwardCompIso.{v, u, w, t} D a b)
      ((abelianSheafPullback.{v, u, w, t} D a).map
          (((abelianSheafAdjunction.{v, u, w, t} D b).homEquiv (M.obj k) (M.obj j)).symm
            (Sheaf.Hom.mk (M.map b))) ≫
        ((abelianSheafAdjunction.{v, u, w, t} D a).homEquiv (M.obj j) (M.obj i)).symm
          (Sheaf.Hom.mk (M.map a)))
    have hpc : (((abelianSheafAdjunction.{v, u, w, t} D b).comp
          (abelianSheafAdjunction.{v, u, w, t} D a)).ofNatIsoRight
            (abelianSheafPushforwardCompIso.{v, u, w, t} D a b)).leftAdjointUniq
          (abelianSheafAdjunction.{v, u, w, t} D (a ≫ b)) =
        abelianSheafPullbackCompIso.{v, u, w, t} D a b := rfl
    rw [hpc] at key
    rw [Equiv.eq_symm_apply,
      ← cancel_mono ((abelianSheafPushforwardCompIso.{v, u, w, t} D a b).inv.app (M.obj i)), key,
      Adjunction.comp_homEquiv]
    dsimp only [Equiv.trans_apply]
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
      Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply]
    have hfin : M.map b ≫ Functor.whiskerLeft (D.u b).op (M.map a) =
        M.map (a ≫ b) ≫
          eqToHom (congrArg (fun H : D.C k ⥤ D.C i => H.op ⋙ (M.obj i).obj) (D.comp a b)) := by
      rw [M.map_comp a b, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    refine Sheaf.hom_ext ?_
    show M.map b ≫ Functor.whiskerLeft (D.u b).op (M.map a) =
      M.map (a ≫ b) ≫
        ((abelianSheafPushforwardCompIso.{v, u, w, t} D a b).inv.app (M.obj i)).hom
    rw [pushforwardCompIso_inv_app_hom.{v, u, w, t} D a b (M.obj i)]
    exact hfin

/-- The direct-image transition of `AbelianCocycleSystem.toAbelianSheafSystem` is the datum it was
built from. -/
theorem transition_toAbelianSheafSystem
    (hid : ∀ i, M.map (𝟙 i) =
      eqToHom (congrArg (fun H : D.C i ⥤ D.C i => H.op ⋙ (M.obj i).obj) (D.id_map i).symm))
    {i j : D.I} (a : i ⟶ j) :
    Stacks.WeakSites.ColimitSiteCohomology.transition.{v, u, w, t} D
      (M.toAbelianSheafSystem hid) a = M.map a := by
  dsimp only [Stacks.WeakSites.ColimitSiteCohomology.transition, toAbelianSheafSystem]
  rw [Equiv.apply_symm_apply]
  rfl

/-- **The system of abelian sheaves obtained from direct-image transition data by splitting the
identity arrows' idempotents.** The sheaf at a level is the image of the idempotent
`AbelianCocycleSystem.idem` there, and the transition is the given one read between those images.

This is the construction the colimit statements of [Stacks, Tag 09YQ] on the levels of
[Stacks, Tag 0EYL] need in order to accept coefficients coming from [Stacks, Tag 0EZL], whose
source imposes only the cocycle law. -/
def split (S : ∀ i, M.Splitting i) :
    AbelianSheafSystem.{v, u, w, t} D :=
  (M.splitCocycle S).toAbelianSheafSystem (M.splitCocycle_map_id S)

/-- The sheaf of the split system at a level is the image of the splitting there. -/
theorem split_obj (S : ∀ i, M.Splitting i) (i : D.I) : (M.split S).obj i = (S i).obj := rfl

/-- The direct-image transition of the split system. -/
theorem transition_split (S : ∀ i, M.Splitting i) {i j : D.I} (a : i ⟶ j) :
    Stacks.WeakSites.ColimitSiteCohomology.transition.{v, u, w, t} D (M.split S) a =
      (S j).incl.hom ≫ M.map a ≫ Functor.whiskerLeft (D.u a).op (S i).proj.hom :=
  transition_toAbelianSheafSystem (M.splitCocycle S) (M.splitCocycle_map_id S) a

end AbelianCocycleSystem

namespace AbelianSheafSystem

variable {D : InverseSystemOfFiniteSites.{v, u, w}}

/-- **A system of abelian sheaves is direct-image transition data satisfying the cocycle law**:
its transition in the direct-image form, with the cocycle law supplied by
`Stacks.WeakSites.ColimitSiteCohomology.transition_comp_eqToHom`.

This is the check that `InverseSystemOfFiniteSites.AbelianCocycleSystem` is the right weakening of
this structure: the cocycle law stated there is exactly the law the transition of a system
satisfies, and by `AbelianSheafSystem.idem_toAbelianCocycleSystem` what the identity law adds is
exactly that the idempotent to be split is already the identity. -/
def toAbelianCocycleSystem (F : AbelianSheafSystem.{v, u, w, t} D) :
    AbelianCocycleSystem.{v, u, w, t} D where
  obj := F.obj
  map a := Stacks.WeakSites.ColimitSiteCohomology.transition.{v, u, w, t} D F a
  map_comp a b := by
    exact Stacks.WeakSites.ColimitSiteCohomology.transition_comp_eqToHom.{v, u, w, t} D F a b

/-- **The idempotent of a system of abelian sheaves is the identity.** So the splitting that
`InverseSystemOfFiniteSites.AbelianCocycleSystem.split` performs is vacuous exactly on the data
that already satisfies the identity law, which is what makes that construction a generalisation
and not a modification. -/
theorem idem_toAbelianCocycleSystem (F : AbelianSheafSystem.{v, u, w, t} D) (i : D.I) :
    F.toAbelianCocycleSystem.idem i = 𝟙 (F.obj i) := by
  refine Sheaf.hom_ext ?_
  show Stacks.WeakSites.ColimitSiteCohomology.transition.{v, u, w, t} D F (𝟙 i) ≫
      eqToHom (congrArg (fun H : D.C i ⥤ D.C i => H.op ⋙ (F.obj i).obj) (D.id_map i)) =
    𝟙 (F.obj i).obj
  rw [Stacks.WeakSites.ColimitSiteCohomology.transition_id_eqToHom.{v, u, w, t} D F i,
    eqToHom_trans, eqToHom_refl]

end AbelianSheafSystem

end InverseSystemOfFiniteSites

namespace Stacks.WeakSites.ColimitSiteCohomology

open InverseSystemOfFiniteSites

variable {D : InverseSystemOfFiniteSites.{v, u, w}} (M : AbelianCocycleSystem.{v, u, w, t} D)

/-- **The identity transition acts as the identity on a compatible family.** Compatibility of the
family at an identity arrow already forces this, as it forces a family for
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.zeroTransitionSystem` to vanish. -/
theorem idem_comp_of_isCompatible {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j) (H : Cᵒᵖ ⥤ Ab.{max u v w t})
    (g : ∀ j, (M.obj j).obj ⟶ (uC j).op ⋙ H)
    (hg : ∀ {j k : D.I} (a : k ⟶ j), g j = M.map a ≫ Functor.whiskerLeft (D.u a).op (g k) ≫
      eqToHom (restrict_eq.{v, u, w, t} D uC hu a H)) (k : D.I) :
    (M.idem k).hom ≫ g k = g k := by
  exact M.idem_comp_eq_self _ (hg (𝟙 k))

/-- **Direct-image transition data satisfying the identity law carries its compatible families to
the system of abelian sheaves it becomes.** The transition of
`AbelianCocycleSystem.toAbelianSheafSystem` is the datum itself, so the two compatibility
conditions are the same statement. -/
theorem isCompatible_toAbelianSheafSystem
    (hid : ∀ i, M.map (𝟙 i) =
      eqToHom (congrArg (fun H : D.C i ⥤ D.C i => H.op ⋙ (M.obj i).obj) (D.id_map i).symm))
    {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j) (H : Cᵒᵖ ⥤ Ab.{max u v w t})
    (g : ∀ j, (M.obj j).obj ⟶ (uC j).op ⋙ H)
    (hg : ∀ {j k : D.I} (a : k ⟶ j), g j = M.map a ≫ Functor.whiskerLeft (D.u a).op (g k) ≫
      eqToHom (restrict_eq.{v, u, w, t} D uC hu a H)) :
    IsCompatible.{v, u, w, t} D uC hu (M.toAbelianSheafSystem hid) H g := by
  intro j k a
  rw [M.transition_toAbelianSheafSystem hid a]
  exact hg a

/-- The compatibility clause of `Stacks.WeakSites.ColimitSiteCohomology.isCompatible_split`, at a
single arrow of the index. -/
theorem splitCocycle_isCompatible_app (S : ∀ i, M.Splitting i) {C : Type w} [SmallCategory C]
    (uC : ∀ i, D.C i ⥤ C) (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (H : Cᵒᵖ ⥤ Ab.{max u v w t}) (g : ∀ j, (M.obj j).obj ⟶ (uC j).op ⋙ H)
    (hg : ∀ {j k : D.I} (a : k ⟶ j), g j = M.map a ≫ Functor.whiskerLeft (D.u a).op (g k) ≫
      eqToHom (restrict_eq.{v, u, w, t} D uC hu a H)) {j k : D.I} (a : k ⟶ j) :
    (S j).incl.hom ≫ g j =
      ((S j).incl.hom ≫ M.map a ≫ Functor.whiskerLeft (D.u a).op (S k).proj.hom) ≫
        Functor.whiskerLeft (D.u a).op ((S k).incl.hom ≫ g k) ≫
          eqToHom (restrict_eq.{v, u, w, t} D uC hu a H) := by
  have hgk : (M.idem k).hom ≫ g k = g k :=
    idem_comp_of_isCompatible M uC hu H g hg k
  have hw : Functor.whiskerLeft (D.u a).op (S k).proj.hom ≫
        Functor.whiskerLeft (D.u a).op ((S k).incl.hom ≫ g k) ≫
          eqToHom (restrict_eq.{v, u, w, t} D uC hu a H) =
      Functor.whiskerLeft (D.u a).op (g k) ≫
        eqToHom (restrict_eq.{v, u, w, t} D uC hu a H) := by
    rw [← Category.assoc, ← Functor.whiskerLeft_comp, ← Category.assoc, M.proj_incl_hom (S k), hgk]
  rw [Category.assoc, Category.assoc, hw, ← hg a]

/-- **A compatible family for direct-image transition data satisfying only the cocycle law is a
compatible family for the split system**, restricted along the inclusions of the splittings.

This is the second half of what the passage of [Stacks, Tag 0EZL] coefficients into the colimit
statements of the levels of [Stacks, Tag 0EYL] owes: `AbelianCocycleSystem.split` supplies the
system, and this supplies the legs. Nothing is assumed of the data beyond the cocycle law. -/
theorem isCompatible_split (S : ∀ i, M.Splitting i) {C : Type w} [SmallCategory C]
    (uC : ∀ i, D.C i ⥤ C) (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (H : Cᵒᵖ ⥤ Ab.{max u v w t}) (g : ∀ j, (M.obj j).obj ⟶ (uC j).op ⋙ H)
    (hg : ∀ {j k : D.I} (a : k ⟶ j), g j = M.map a ≫ Functor.whiskerLeft (D.u a).op (g k) ≫
      eqToHom (restrict_eq.{v, u, w, t} D uC hu a H)) :
    IsCompatible.{v, u, w, t} D uC hu (M.split S) H (fun j => (S j).incl.hom ≫ g j) :=
  isCompatible_toAbelianSheafSystem (M.splitCocycle S) (M.splitCocycle_map_id S) uC hu H
    (fun j => (S j).incl.hom ≫ g j)
    (fun a => splitCocycle_isCompatible_app M S uC hu H g hg a)

end Stacks.WeakSites.ColimitSiteCohomology

namespace InverseSystemOfFiniteSites.AbelianCocycleSystem

open Stacks.WeakSites.ColimitSiteCohomology

variable {D : InverseSystemOfFiniteSites.{v, u, w}} (M : AbelianCocycleSystem.{v, u, w, t} D)

/-- **A family of maps out of direct-image transition data is compatible with the transitions.**
The condition `Stacks.WeakSites.ColimitSiteCohomology.IsCompatible` imposes on a family out of an
`InverseSystemOfFiniteSites.AbelianSheafSystem`, read off data that satisfies only the cocycle
law. -/
def IsCompatible {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j) (H : Cᵒᵖ ⥤ Ab.{max u v w t})
    (g : ∀ j, (M.obj j).obj ⟶ (uC j).op ⋙ H) : Prop :=
  ∀ {j k : D.I} (a : k ⟶ j), g j = M.map a ≫ Functor.whiskerLeft (D.u a).op (g k) ≫
    eqToHom (restrict_eq.{v, u, w, t} D uC hu a H)

/-- **`𝒢` with the family `ι` presents `colim fᵢ⁻¹Fᵢ` for direct-image transition data satisfying
only the cocycle law.** The predicate
`Stacks.WeakSites.ColimitSiteCohomology.IsColimitPresentation` read off such data: the family is
compatible, and every compatible family of maps to an abelian sheaf on the colimit site factors
uniquely through it. -/
def IsColimitPresentation {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
    (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j) (K : Precoverage C)
    (𝒢 : Sheaf K.toGrothendieck (Ab.{max u v w t}))
    (ι : ∀ j, (M.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj) : Prop :=
  M.IsCompatible uC hu 𝒢.obj ι ∧
    ∀ (H : Sheaf K.toGrothendieck (Ab.{max u v w t}))
      (g : ∀ j, (M.obj j).obj ⟶ (uC j).op ⋙ H.obj),
      M.IsCompatible uC hu H.obj g →
        ∃! h : 𝒢 ⟶ H, ∀ j, ι j ≫ Functor.whiskerLeft (uC j).op h.hom = g j

/-- **A colimit presentation for direct-image transition data satisfying only the cocycle law is a
colimit presentation for the split system**, with the legs restricted along the inclusions of the
splittings. The sheaf on the colimit site is unchanged.

This is the whole of what the passage of [Stacks, Tag 0EZL] coefficients into the colimit
statements on the levels of [Stacks, Tag 0EYL] owes on the coefficient side: a crossing that
produces cocycle data on the levels together with a presentation of it needs nothing further, the
identity law and the presentation for a genuine
`InverseSystemOfFiniteSites.AbelianSheafSystem` both following from here.

Compatibility is `Stacks.WeakSites.ColimitSiteCohomology.isCompatible_split`. For the universal
property, a compatible family `g` for the split system is carried back along the projections to a
compatible family for the original data — compatibility survives because the idempotent acts as
the identity on every transition — and the factorisation it has there factors `g` itself, the
inclusion and the projection composing to the identity. Uniqueness transfers because the
idempotent acts as the identity on `ι` as well, by
`Stacks.WeakSites.ColimitSiteCohomology.idem_comp_of_isCompatible`. -/
theorem isColimitPresentation_split (S : ∀ i, M.Splitting i) {C : Type w} [SmallCategory C]
    (uC : ∀ i, D.C i ⥤ C) (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
    (K : Precoverage C) (𝒢 : Sheaf K.toGrothendieck (Ab.{max u v w t}))
    (ι : ∀ j, (M.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)
    (h : M.IsColimitPresentation uC hu K 𝒢 ι) :
    Stacks.WeakSites.ColimitSiteCohomology.IsColimitPresentation.{v, u, w, t} D uC hu K
      (M.split S) 𝒢 (fun j => (S j).incl.hom ≫ ι j) := by
  have hιj : ∀ j : D.I, (M.idem j).hom ≫ ι j = ι j :=
    fun j => idem_comp_of_isCompatible M uC hu 𝒢.obj ι h.1 j
  refine ⟨isCompatible_split M S uC hu 𝒢.obj ι h.1, ?_⟩
  intro H g' hg'
  obtain ⟨g, hgdef⟩ : ∃ g : ∀ j : D.I, ((S j).obj).obj ⟶ (uC j).op ⋙ H.obj,
      ∀ j, g j = g' j := ⟨g', fun _ => rfl⟩
  have hg : M.IsCompatible uC hu H.obj (fun j => (S j).proj.hom ≫ g j) := by
    intro j k a
    have e : g j =
        ((S j).incl.hom ≫ M.map a ≫ Functor.whiskerLeft (D.u a).op (S k).proj.hom) ≫
          Functor.whiskerLeft (D.u a).op (g k) ≫
            eqToHom (restrict_eq.{v, u, w, t} D uC hu a H.obj) := by
      rw [hgdef j, hgdef k, ← M.transition_split S a]
      exact hg' a
    have hkey : (S j).proj.hom ≫ (S j).incl.hom ≫ M.map a = M.map a := by
      rw [← Category.assoc, M.proj_incl_hom (S j), M.idem_comp_map a]
    show (S j).proj.hom ≫ g j = M.map a ≫
      Functor.whiskerLeft (D.u a).op ((S k).proj.hom ≫ g k) ≫
        eqToHom (restrict_eq.{v, u, w, t} D uC hu a H.obj)
    rw [e, Functor.whiskerLeft_comp]
    simp only [Category.assoc]
    rw [reassoc_of% hkey]
  obtain ⟨h₀, hh₀, huniq⟩ := h.2 H (fun j => (S j).proj.hom ≫ g j) hg
  refine ⟨h₀, ?_, ?_⟩
  · intro j
    have e0 : ι j ≫ Functor.whiskerLeft (uC j).op h₀.hom = (S j).proj.hom ≫ g j := hh₀ j
    show ((S j).incl.hom ≫ ι j) ≫ Functor.whiskerLeft (uC j).op h₀.hom = g' j
    rw [← hgdef j, Category.assoc, e0, ← Category.assoc, M.incl_proj_hom (S j), Category.id_comp]
  · intro h' hh'
    refine huniq h' ?_
    intro j
    have e1 : ((S j).incl.hom ≫ ι j) ≫ Functor.whiskerLeft (uC j).op h'.hom = g' j := hh' j
    rw [← hgdef j] at e1
    show ι j ≫ Functor.whiskerLeft (uC j).op h'.hom = (S j).proj.hom ≫ g j
    rw [← e1, ← Category.assoc, ← Category.assoc, M.proj_incl_hom (S j), hιj j]

end InverseSystemOfFiniteSites.AbelianCocycleSystem

end
