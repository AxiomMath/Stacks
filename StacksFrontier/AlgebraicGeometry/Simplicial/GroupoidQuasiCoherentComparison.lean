module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.QuasicoherentPullbackFunctor
public import StacksFrontier.AlgebraicGeometry.Groupoids.DescentIso
public import StacksFrontier.AlgebraicGeometry.Simplicial.GroupoidNerveDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite

/-!
# Quasi-coherent modules on a groupoid scheme and on the total Zariski site of its nerve

Let `S` be a scheme and `(U,R,s,t,c)` a groupoid scheme over `S`, with `X` the simplicial scheme
of **Stacks 07TN**.  The category of quasi-coherent modules on `(U,R,s,t,c)` in the sense of
**Stacks 03LI** is equivalent to the category of quasi-coherent modules on `X_{Zar}`.  This is
**Stacks 07TP**.

The part of that statement which the source's one-line proof passes over is the normalization of
a descent morphism along the identity section: the data `(ℱ, α)` produced by the pair
description of Stacks 07TH carries only the degree-two cocycle condition, while Stacks 03LI also
demands `e^*α = id`.  That normalization is proved here, together with its
converse.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.DescentData` is a quasi-coherent module on the object scheme
  with an invertible descent morphism satisfying the cocycle condition, without the
  normalization along the identity section.
* `Stacks.Groupoids.GroupoidScheme.GroupoidSimplicialScheme.descentDataToPair` sends a
  descent datum to the pair on the total Zariski site of the nerve: the pullback of the module to
  degree zero with the descent morphism transported to the faces of degree one.

## Main results

* `Stacks.Groupoids.GroupoidScheme.reindexHom_compose` is the composition law of a descent
  morphism satisfying the cocycle condition: reindexing along a composite of two composable
  generalized arrows is the composite of the reindexings.
* `Stacks.Groupoids.GroupoidScheme.identityDescent_comp_self` and
  `Stacks.Groupoids.GroupoidScheme.identityDescent_eq_id_of_cocycle` are the identity
  normalization: `e^*α` is idempotent, hence is the identity when `α` is invertible.
* `Stacks.Groupoids.GroupoidScheme.isIso_of_cocycle_of_identity` is the converse: a normalized
  descent morphism satisfying the cocycle condition is invertible.
* `Stacks.Groupoids.GroupoidScheme.descentDataEquivQuasicoherentModule` is the resulting
  equivalence of descent data with the quasi-coherent modules of Stacks 03LI.
* `Stacks.Groupoids.GroupoidScheme.GroupoidSimplicialScheme.isCocycle_asIso_transportHom_iff`:
  the cocycle condition of a pair on the nerve is the cocycle condition of the groupoid.
* `Stacks.Groupoids.GroupoidScheme.GroupoidSimplicialScheme.descentDataEquivPair`: descent data
  are the quasi-coherent pairs on the nerve.
* `Stacks.Groupoids.GroupoidScheme.quasicoherentModuleEquivQuasicoherentOnTotalSite` is
  **Stacks 07TP**.

## Implementation notes

The pullback of sheaves of modules is a pseudofunctor, so reindexing a descent morphism along a
composite agrees with reindexing twice only up to the comparison between the two bracketings of
the composite.  The calculus of `Stacks.Groupoids.reindexHom` in the base morphism is already
available: `Stacks.Groupoids.reindexHom_assoc_rev`, `Stacks.Groupoids.reindexHom_id_left`,
`Stacks.Groupoids.reindexHom_congr` and `Stacks.Groupoids.reindexHom_congr_source` state the
associativity and unit coherences and the transport along equal morphisms, and
`Stacks.Groupoids.GroupoidScheme.reindexHom_successiveDescent` reindexes the successive-descent
morphism through the two projections.  Those lemmas phrase the comparisons as
`AlgebraicGeometry.Scheme.Modules.pullbackCongr`, which
`Stacks.Modules.pullbackCongr_hom_app` turns into the canonical `eqToHom`; every transport
appearing below is such an `eqToHom`, so the transports compose away.

The composition law `reindexHom_compose` is the cocycle condition reindexed along the morphism
`pullback.lift a b w` into the scheme of composable arrows.  Applied to the pair of identity
arrows at an object it makes `e^*α` idempotent, and applied to the two sections given by the
inverse of the groupoid it exhibits a left and a right inverse of the pullback of `α` along the
identity arrow of `R`.  The latter argument is the unbundled form of
`Stacks.Groupoids.GroupoidScheme.QuasicoherentModule.alpha_isIso`: it needs neither the
quasi-coherence of the module nor the bundled datum, only the cocycle condition and the
normalization, which is what makes the equivalence with `DescentData` go through.

The total Zariski site `X_{Zar}` is `AlgebraicGeometry.SimplicialScheme.zariskiTopology` of the
underlying simplicial scheme, with the structure sheaf of
`AlgebraicGeometry.SimplicialScheme.zariskiRingedTopos`; its quasi-coherent modules are compared
with pairs by `AlgebraicGeometry.SimplicialScheme.quasicoherentEquivQuasicoherentPair`
(Stacks 07TH and Stacks 0D7M).  The comparison of pairs with descent data reads the cocycle
condition of a pair in reindexed form
(`AlgebraicGeometry.SimplicialScheme.isCocycle_iff_reindexCocycle`) and moves it along the
identifications of the nerve in degrees one and two.

## References

* [Stacks Project, Tag 07TP](https://stacks.math.columbia.edu/tag/07TP)
* [Stacks Project, Tag 07TN](https://stacks.math.columbia.edu/tag/07TN)
* [Stacks Project, Tag 07TI](https://stacks.math.columbia.edu/tag/07TI)
* [Stacks Project, Tag 07TH](https://stacks.math.columbia.edu/tag/07TH)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
* [Stacks Project, Tag 03LI](https://stacks.math.columbia.edu/tag/03LI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Groupoids

namespace GroupoidScheme

variable {S : Scheme.{u}} (G : GroupoidScheme S)

/-- The target of a composite of two composable generalized arrows is the target of the first. -/
theorem compose_left_target {T : Over S} (a b m : T ⟶ G.arrows)
    (w : a ≫ G.source = b ≫ G.target) (hm : pullback.lift a b w ≫ G.comp = m) :
    m.left ≫ G.target.left = a.left ≫ G.target.left := by
  rw [← Over.comp_left, ← Over.comp_left, ← hm, Category.assoc, G.target_comp,
    ← Category.assoc, pullback.lift_fst]

/-- The source of a composite of two composable generalized arrows is the source of the
second. -/
theorem compose_left_source {T : Over S} (a b m : T ⟶ G.arrows)
    (w : a ≫ G.source = b ≫ G.target) (hm : pullback.lift a b w ≫ G.comp = m) :
    m.left ≫ G.source.left = b.left ≫ G.source.left := by
  rw [← Over.comp_left, ← Over.comp_left, ← hm, Category.assoc, G.source_comp,
    ← Category.assoc, pullback.lift_snd]

/-- **The composition law of a groupoid descent morphism.** If `α : t^*F ⟶ s^*F` satisfies the
cocycle condition on the scheme of composable arrows, then reindexing `α` along a composite
`m` of two composable generalized arrows `a` and `b` is the composite of the reindexings along
`a` and along `b`, the three transports being those induced by the identities
`m ≫ t = a ≫ t`, `a ≫ s = b ≫ t` and `b ≫ s = m ≫ s`. -/
theorem reindexHom_compose {T : Over S} (a b m : T ⟶ G.arrows)
    (w : a ≫ G.source = b ≫ G.target) (hm : pullback.lift a b w ≫ G.comp = m)
    {F : G.objects.left.Modules}
    (α : (Scheme.Modules.pullback G.target.left).obj F ⟶
      (Scheme.Modules.pullback G.source.left).obj F)
    (hα : successiveDescent G α = reindexHom G.comp.left α) :
    reindexHom m.left α =
      eqToHom (show (Scheme.Modules.pullback (m.left ≫ G.target.left)).obj F =
          (Scheme.Modules.pullback (a.left ≫ G.target.left)).obj F by
          rw [compose_left_target G a b m w hm]) ≫
        reindexHom a.left α ≫
        eqToHom (show (Scheme.Modules.pullback (a.left ≫ G.source.left)).obj F =
            (Scheme.Modules.pullback (b.left ≫ G.target.left)).obj F by
          rw [← Over.comp_left, ← Over.comp_left, w]) ≫
        reindexHom b.left α ≫
        eqToHom (show (Scheme.Modules.pullback (b.left ≫ G.source.left)).obj F =
            (Scheme.Modules.pullback (m.left ≫ G.source.left)).obj F by
          rw [compose_left_source G a b m w hm]) := by
  have hfst : (pullback.lift a b w).left ≫ (pullback.fst G.source G.target).left = a.left := by
    rw [← Over.comp_left, pullback.lift_fst]
  have hsnd : (pullback.lift a b w).left ≫ (pullback.snd G.source G.target).left = b.left := by
    rw [← Over.comp_left, pullback.lift_snd]
  have hcm : (pullback.lift a b w).left ≫ G.comp.left = m.left := by
    rw [← Over.comp_left, hm]
  have e₁ : (pullback.lift a b w).left ≫ G.comp.left ≫ G.target.left =
      ((pullback.lift a b w).left ≫ (pullback.fst G.source G.target).left) ≫
        G.target.left := by
    rw [hfst, ← Category.assoc, hcm, compose_left_target G a b m w hm]
  have e₂ : ((pullback.lift a b w).left ≫ (pullback.fst G.source G.target).left) ≫
      G.source.left =
      ((pullback.lift a b w).left ≫ (pullback.snd G.source G.target).left) ≫
        G.target.left := by
    rw [hfst, hsnd, ← Over.comp_left, ← Over.comp_left, w]
  have e₃ : ((pullback.lift a b w).left ≫ (pullback.snd G.source G.target).left) ≫
      G.source.left = (pullback.lift a b w).left ≫ G.comp.left ≫ G.source.left := by
    rw [hsnd, ← Category.assoc, hcm, compose_left_source G a b m w hm]
  have key := congrArg (reindexHom (pullback.lift a b w).left) hα
  rw [reindexHom_successiveDescent G (pullback.lift a b w).left α e₁ e₂ e₃,
    reindexHom_assoc_rev, reindexHom_congr_source hfst α, reindexHom_congr_source hsnd α,
    reindexHom_congr_source hcm α] at key
  simp only [Stacks.Modules.pullbackCongr_hom_app, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc] at key
  rw [(comp_eqToHom_iff _ _ _).mp ((eqToHom_comp_iff _ _ _).mp key.symm)]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

/-- **The identity normalization.** A groupoid descent morphism satisfying the cocycle condition
has idempotent pullback along the identity section: the endomorphism `e^*α` of `F` is an
idempotent of `F`.

Reindexing the cocycle condition along the section of the scheme of composable arrows which
sends an object to the pair of identity arrows at it expresses `e^*α` as `e^*α ∘ e^*α`. -/
theorem identityDescent_comp_self {F : G.objects.left.Modules}
    (α : (Scheme.Modules.pullback G.target.left).obj F ⟶
      (Scheme.Modules.pullback G.source.left).obj F)
    (hα : successiveDescent G α = reindexHom G.comp.left α) :
    identityDescent G α ≫ identityDescent G α = identityDescent G α := by
  have he : G.identity ≫ G.target ≫ G.identity = G.identity := by
    rw [← Category.assoc, G.target_identity, Category.id_comp]
  have w : (G.identity : G.objects ⟶ G.arrows) ≫ G.source = G.identity ≫ G.target := by
    rw [G.source_identity, G.target_identity]
  have hw : ((G.identity : G.objects ⟶ G.arrows) ≫ G.target ≫ G.identity) ≫ G.source =
      G.identity ≫ G.target := by
    rw [he, G.source_identity, G.target_identity]
  have hm : pullback.lift G.identity G.identity w ≫ G.comp = G.identity := by
    have h := G.left_identity G.objects G.identity hw
    rwa [show pullback.lift (G.identity ≫ G.target ≫ G.identity) G.identity hw =
      pullback.lift G.identity G.identity w by
      refine pullback.hom_ext ?_ ?_ <;> simp [he]] at h
  have hid := reindexHom_compose G G.identity G.identity G.identity w hm α hα
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hid
  rw [identityDescent]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Stacks.Modules.pullbackCongr_hom_app,
    eqToHom_trans_assoc]
  rw [reassoc_of% hid.symm]

/-- Reindexing an invertible descent morphism is invertible. -/
theorem isIso_reindexHom {V W X' : Scheme.{u}} (f : V ⟶ W) {g h : W ⟶ X'} {F : X'.Modules}
    (α : (Scheme.Modules.pullback g).obj F ⟶ (Scheme.Modules.pullback h).obj F) [IsIso α] :
    IsIso (reindexHom f α) := by
  rw [reindexHom]
  infer_instance

/-- The pullback of an invertible descent morphism along the identity section is invertible. -/
theorem isIso_identityDescent {F : G.objects.left.Modules}
    (α : (Scheme.Modules.pullback G.target.left).obj F ⟶
      (Scheme.Modules.pullback G.source.left).obj F) [IsIso α] :
    IsIso (identityDescent G α) := by
  have := isIso_reindexHom G.identity.left α
  rw [identityDescent]
  infer_instance

/-- **The identity normalization, Stacks 03LI (c) from Stacks 03LI (b).** An invertible groupoid
descent morphism satisfying the cocycle condition is normalized along the identity section:
`e^*α = id`.

The cocycle condition makes `e^*α` an idempotent endomorphism of `F`, and an invertible
idempotent is the identity.  This is a different hypothesis from the one of
`Stacks.Groupoids.GroupoidScheme.identityDescent_eq_id`, which reads the normalization off a
reindexing that is already the canonical comparison. -/
theorem identityDescent_eq_id_of_cocycle {F : G.objects.left.Modules}
    (α : (Scheme.Modules.pullback G.target.left).obj F ⟶
      (Scheme.Modules.pullback G.source.left).obj F) [IsIso α]
    (hα : successiveDescent G α = reindexHom G.comp.left α) :
    identityDescent G α = 𝟙 F := by
  have := isIso_identityDescent G α
  simpa using congrArg (inv (identityDescent G α) ≫ ·) (identityDescent_comp_self G α hα)

/-- A morphism which becomes an isomorphism when composed with isomorphisms on both sides is
an isomorphism. -/
theorem isIso_of_comp_eq {C : Type*} [Category C] {A B P Q : C} (p : A ⟶ P) (f : P ⟶ Q)
    (q : Q ⟶ B) (w : A ⟶ B) [IsIso p] [IsIso q] [IsIso w] (h : p ≫ f ≫ q = w) : IsIso f := by
  have hf : f = inv p ≫ w ≫ inv q := by
    rw [← h]
    simp
  rw [hf]
  infer_instance

/-- A factorization of an isomorphism whose last factor is invertible exhibits a retraction of
the middle factor. -/
theorem retraction_of_comp_eq {C : Type*} [Category C] {A B P Q : C} (p : A ⟶ P) (f : P ⟶ Q)
    (q : Q ⟶ B) (w : A ⟶ B) [IsIso q] [IsIso w] (h : p ≫ f ≫ q = w) :
    (q ≫ inv w ≫ p) ≫ f = 𝟙 Q := by
  have h1 : p ≫ f = w ≫ inv q := by
    rw [← h]
    simp
  rw [Category.assoc, Category.assoc, h1]
  simp

/-- A factorization of an isomorphism whose first factor is invertible exhibits a section of the
middle factor. -/
theorem section_of_comp_eq {C : Type*} [Category C] {A B P Q : C} (p : A ⟶ P) (f : P ⟶ Q)
    (q : Q ⟶ B) (w : A ⟶ B) [IsIso p] [IsIso w] (h : p ≫ f ≫ q = w) :
    f ≫ (q ≫ inv w ≫ p) = 𝟙 P := by
  have h1 : f ≫ q = inv p ≫ w := by
    rw [← h]
    simp
  rw [← Category.assoc, h1]
  simp

/-- A morphism with a left and a right inverse is an isomorphism. -/
theorem isIso_of_retraction_of_section {C : Type*} [Category C] {P Q : C} (f : P ⟶ Q)
    (r : Q ⟶ P) (hr : r ≫ f = 𝟙 Q) (l : Q ⟶ P) (hl : f ≫ l = 𝟙 P) : IsIso f := by
  have hlr : l = r := by
    rw [← Category.id_comp l, ← hr, Category.assoc, hl, Category.comp_id]
  exact ⟨l, hl, by rw [hlr, hr]⟩

/-- The pullback of a normalized descent morphism along the identity section is invertible: by
`Stacks.Groupoids.GroupoidScheme.reindexHom_identity` it is a composite of the canonical
comparisons of pullbacks. -/
theorem isIso_reindexHom_identity {F : G.objects.left.Modules}
    (α : (Scheme.Modules.pullback G.target.left).obj F ⟶
      (Scheme.Modules.pullback G.source.left).obj F)
    (hident : identityDescent G α = 𝟙 F) :
    IsIso (reindexHom G.identity.left α) := by
  rw [reindexHom_identity G α hident]
  infer_instance

/-- **A normalized descent morphism is invertible.**  If `α : t^*F ⟶ s^*F` satisfies the cocycle
condition and `e^*α = id`, then `α` is an isomorphism.

Reindexing the cocycle condition along the two sections `(i, id)` and `(id, i)` of the scheme of
composable arrows given by the inverse of the groupoid expresses the pullback of `α` along the
identity arrow `id_R` as a factor of the pullback of `α` along `s ≫ e` and along `t ≫ e`; both
of the latter are invertible because `e^*α` is, so the former has a left and a right inverse. -/
theorem isIso_of_cocycle_of_identity {F : G.objects.left.Modules}
    (α : (Scheme.Modules.pullback G.target.left).obj F ⟶
      (Scheme.Modules.pullback G.source.left).obj F)
    (hα : successiveDescent G α = reindexHom G.comp.left α)
    (hident : identityDescent G α = 𝟙 F) :
    IsIso α := by
  have w₁ : (G.inverse : G.arrows ⟶ G.arrows) ≫ G.source = (𝟙 G.arrows) ≫ G.target := by
    rw [G.source_inverse, Category.id_comp]
  have hm₁ : pullback.lift G.inverse (𝟙 G.arrows) w₁ ≫ G.comp = G.source ≫ G.identity := by
    simpa using G.left_inverse G.arrows (𝟙 G.arrows) (by simp [G.source_inverse])
  have w₂ : (𝟙 G.arrows) ≫ G.source = (G.inverse : G.arrows ⟶ G.arrows) ≫ G.target := by
    rw [Category.id_comp, G.target_inverse]
  have hm₂ : pullback.lift (𝟙 G.arrows) G.inverse w₂ ≫ G.comp = G.target ≫ G.identity := by
    simpa using G.right_inverse G.arrows (𝟙 G.arrows) (by simp [G.target_inverse])
  have hL := reindexHom_compose G G.inverse (𝟙 G.arrows) (G.source ≫ G.identity) w₁ hm₁ α hα
  have hR := reindexHom_compose G (𝟙 G.arrows) G.inverse (G.target ≫ G.identity) w₂ hm₂ α hα
  have hβ : IsIso (reindexHom G.identity.left α) := isIso_reindexHom_identity G α hident
  have hW : ∀ f : G.arrows ⟶ G.objects, IsIso (reindexHom (f ≫ G.identity).left α) := fun f =>
    have := isIso_reindexHom f.left (reindexHom G.identity.left α)
    isIso_of_comp_eq _ _ _ (reindexHom f.left (reindexHom G.identity.left α))
      (reindexHom_assoc_rev f.left G.identity.left α).symm
  have hWL := hW G.source
  have hWR := hW G.target
  have hL' := hL.symm
  rw [← Category.assoc, ← Category.assoc] at hL'
  have hr := retraction_of_comp_eq _ _ _ _ hL'
  have hs := section_of_comp_eq _ _ _ _ hR.symm
  have hδ : IsIso (reindexHom (𝟙 G.arrows.left) α) :=
    isIso_of_retraction_of_section _ _ hr _ hs
  exact isIso_of_comp_eq _ α _ (reindexHom (𝟙 G.arrows.left) α) (reindexHom_id_left α).symm

/-! ### Descent data and the quasi-coherent modules of Stacks 03LI -/

/-- **Groupoid descent data.** A quasi-coherent module `F` on the object scheme together with an
*invertible* descent morphism `α : t^*F ⟶ s^*F` satisfying the cocycle condition on the scheme
of composable arrows.  This is the data that a pair `(F, α)` on the total Zariski site of the
nerve produces; the normalization `e^*α = id` of Stacks 03LI is not part of it. -/
structure DescentData {S : Scheme.{u}} (G : GroupoidScheme S) where
  /-- The module on the object scheme. -/
  module : G.objects.left.Modules
  /-- The underlying module is quasi-coherent. -/
  isQuasicoherent : module.IsQuasicoherent
  /-- The descent morphism from pullback along the target to pullback along the source. -/
  alpha : (Scheme.Modules.pullback G.target.left).obj module ⟶
    (Scheme.Modules.pullback G.source.left).obj module
  /-- The descent morphism is invertible. -/
  isIso_alpha : IsIso alpha
  /-- The cocycle condition on the scheme of composable arrows. -/
  cocycle : successiveDescent G alpha = reindexHom G.comp.left alpha

namespace DescentData

variable {S : Scheme.{u}} {G : GroupoidScheme S}

/-- A morphism of descent data is a morphism of the underlying modules which intertwines the
descent morphisms. -/
@[ext]
structure Hom (A B : DescentData G) where
  /-- The morphism of underlying modules on the object scheme. -/
  hom : A.module ⟶ B.module
  /-- Compatibility with the descent morphisms. -/
  comm : A.alpha ≫ (Scheme.Modules.pullback G.source.left).map hom =
    (Scheme.Modules.pullback G.target.left).map hom ≫ B.alpha

/-- Descent data on a groupoid scheme and their compatible module morphisms form a category. -/
instance : Category (DescentData G) where
  Hom := Hom
  id A := { hom := 𝟙 A.module, comm := by simp }
  comp f g :=
    { hom := f.hom ≫ g.hom
      comm := by rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, f.comm,
        Category.assoc, g.comm, ← Category.assoc] }
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp

end DescentData

/-- **The identity normalization, as a functor.** Descent data on a groupoid scheme are
quasi-coherent modules on it in the sense of Stacks 03LI: the normalization `e^*α = id` holds
automatically for an invertible descent morphism satisfying the cocycle condition. -/
noncomputable def descentDataToQuasicoherentModule (G : GroupoidScheme S) :
    DescentData G ⥤ QuasicoherentModule G where
  obj A :=
    { module := A.module
      isQuasicoherent := A.isQuasicoherent
      alpha := A.alpha
      cocycle := A.cocycle
      identity :=
        letI := A.isIso_alpha; identityDescent_eq_id_of_cocycle G A.alpha A.cocycle }
  map f := { hom := f.hom, comm := f.comm }

/-- **Invertibility, as a functor.** A quasi-coherent module on a groupoid scheme in the sense
of Stacks 03LI is a descent datum: its descent morphism is invertible. -/
noncomputable def quasicoherentModuleToDescentData (G : GroupoidScheme S) :
    QuasicoherentModule G ⥤ DescentData G where
  obj M :=
    { module := M.module
      isQuasicoherent := M.isQuasicoherent
      alpha := M.alpha
      isIso_alpha := isIso_of_cocycle_of_identity G M.alpha M.cocycle M.identity
      cocycle := M.cocycle }
  map f := { hom := f.hom, comm := f.comm }

/-- **Descent data are the quasi-coherent modules of Stacks 03LI.** Requiring the descent
morphism to be invertible and requiring it to be normalized along the identity section cut out
the same category: the normalization follows from invertibility and the cocycle condition, and
conversely invertibility follows from the normalization and the cocycle condition. -/
noncomputable def descentDataEquivQuasicoherentModule (G : GroupoidScheme S) :
    DescentData G ≌ QuasicoherentModule G where
  functor := descentDataToQuasicoherentModule G
  inverse := quasicoherentModuleToDescentData G
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-! ### The total Zariski site of the simplicial scheme of a groupoid scheme -/

section TotalSite

open AlgebraicGeometry.SimplicialScheme
open scoped Simplicial

namespace GroupoidSimplicialScheme

variable {G} (N : GroupoidSimplicialScheme G)

/-- The simplicial scheme of Stacks 07TN, with the structure morphisms to `S` forgotten. -/
abbrev toSchemes : SimplicialObject Scheme.{u} := N.simplicialScheme ⋙ Over.forget S

/-- The underlying morphism of schemes of `N.objectsIso.hom` is an isomorphism. -/
instance isIso_objectsIso_hom_left : IsIso N.objectsIso.hom.left :=
  (Over.forget S).map_isIso N.objectsIso.hom

/-- The underlying morphism of schemes of `N.arrowsIso.hom` is an isomorphism. -/
instance isIso_arrowsIso_hom_left : IsIso N.arrowsIso.hom.left :=
  (Over.forget S).map_isIso N.arrowsIso.hom

/-- The underlying morphism of schemes of `N.composablePairsIso.hom` is an isomorphism. -/
instance isIso_composablePairsIso_hom_left : IsIso N.composablePairsIso.hom.left :=
  (Over.forget S).map_isIso N.composablePairsIso.hom

/-- The face `δ¹₁` of the nerve is the target map. -/
theorem face_one_one :
    N.toSchemes.map (SimplexCategory.δ (1 : Fin 2)).op ≫ N.objectsIso.hom.left =
      N.arrowsIso.hom.left ≫ G.target.left :=
  congrArg (fun f => f.left) N.delta_one_one

/-- The face `δ¹₀` of the nerve is the source map. -/
theorem face_one_zero :
    N.toSchemes.map (SimplexCategory.δ (0 : Fin 2)).op ≫ N.objectsIso.hom.left =
      N.arrowsIso.hom.left ≫ G.source.left :=
  congrArg (fun f => f.left) N.delta_one_zero

/-- The face `δ²₀` of the nerve is the second projection. -/
theorem face_two_zero :
    N.toSchemes.map (@SimplexCategory.δ (0 + 1) (0 : Fin 3)).op ≫ N.arrowsIso.hom.left =
      N.composablePairsIso.hom.left ≫ (pullback.snd G.source G.target).left :=
  congrArg (fun f => f.left) N.delta_two_zero

/-- The face `δ²₁` of the nerve is the composition law. -/
theorem face_two_one :
    N.toSchemes.map (@SimplexCategory.δ (0 + 1) (1 : Fin 3)).op ≫ N.arrowsIso.hom.left =
      N.composablePairsIso.hom.left ≫ G.comp.left :=
  congrArg (fun f => f.left) N.delta_two_one

/-- The face `δ²₂` of the nerve is the first projection. -/
theorem face_two_two :
    N.toSchemes.map (@SimplexCategory.δ (0 + 1) (2 : Fin 3)).op ≫ N.arrowsIso.hom.left =
      N.composablePairsIso.hom.left ≫ (pullback.fst G.source G.target).left :=
  congrArg (fun f => f.left) N.delta_two_two

/-- **The cocycle condition on the nerve is the cocycle condition of the groupoid.** A descent
morphism `γ : t^*ℱ ⟶ s^*ℱ`, transported to the faces of degree one of the nerve, satisfies the
cocycle condition of a pair exactly when it satisfies the cocycle condition on the scheme of
composable arrows. -/
theorem isCocycle_asIso_transportHom_iff {M : G.objects.left.Modules}
    (γ : (Scheme.Modules.pullback G.target.left).obj M ⟶
      (Scheme.Modules.pullback G.source.left).obj M) [IsIso γ] :
    (zariskiModuleFamily N.toSchemes).IsCocycle
        ((Scheme.Modules.pullback N.objectsIso.hom.left).obj M)
        (asIso (transportHom N.face_one_one N.face_one_zero γ)) ↔
      successiveDescent G γ = reindexHom G.comp.left γ := by
  have g₂₁ : (pullback.fst G.source G.target).left ≫ G.target.left =
      G.comp.left ≫ G.target.left := (congrArg Over.Hom.left G.target_comp).symm
  have g₂₀ : (pullback.fst G.source G.target).left ≫ G.source.left =
      (pullback.snd G.source G.target).left ≫ G.target.left :=
    congrArg Over.Hom.left (pullback.condition : pullback.fst G.source G.target ≫ G.source =
      pullback.snd G.source G.target ≫ G.target)
  have g₀₁ : (pullback.snd G.source G.target).left ≫ G.source.left =
      G.comp.left ≫ G.source.left := (congrArg Over.Hom.left G.source_comp).symm
  refine (isCocycle_iff_reindexCocycle N.toSchemes _ _).trans
    ((reindexCocycle_transportHom_iff _ _ _ N.face_one_one N.face_one_zero γ _ _ _
      (by rw [Category.assoc, Category.assoc, ← N.face_one_one,
        reassoc_of% map_delta_two_one])
      (by rw [Category.assoc, Category.assoc, ← N.face_one_zero, ← N.face_one_one,
        reassoc_of% map_delta_two_zero])
      (by rw [Category.assoc, Category.assoc, ← N.face_one_zero,
        reassoc_of% map_delta_zero_one])).trans
    ((reindexCocycle_congr N.face_two_zero N.face_two_one N.face_two_two _ _ _
      (by rw [Category.assoc, Category.assoc, g₂₁])
      (by rw [Category.assoc, Category.assoc, g₂₀])
      (by rw [Category.assoc, Category.assoc, g₀₁]) γ).trans
    ((reindexCocycle_comp_iff N.composablePairsIso.hom.left _ _ _ _ _ g₂₁ g₂₀ g₀₁ _ _ _ γ).trans
      (groupoid_cocycle_iff_reindexCocycle G γ).symm)))

/-- **The pair on the nerve of a descent datum.** The pullback of the module to the degree-zero
part of the nerve, with the descent morphism transported to the faces of degree one. -/
noncomputable def descentDataToPairFunctor :
    DescentData G ⥤ (zariskiModuleFamily N.toSchemes).Pair where
  obj A :=
    { obj := (Scheme.Modules.pullback N.objectsIso.hom.left).obj A.module
      iso := letI := A.isIso_alpha; asIso (transportHom N.face_one_one N.face_one_zero A.alpha)
      cocycle := letI := A.isIso_alpha; (N.isCocycle_asIso_transportHom_iff A.alpha).2 A.cocycle }
  map {A B} f :=
    { map := (Scheme.Modules.pullback N.objectsIso.hom.left).map f.hom
      comm := by
        dsimp only [zariskiModuleFamily_map, asIso_hom]
        rw [← map_comp_transportHom, ← transportHom_comp_map, f.comm] }
  map_id A := SimplicialPseudoFamily.Pair.hom_ext (by
    simp only [SimplicialPseudoFamily.Pair.id_map]
    exact (Scheme.Modules.pullback N.objectsIso.hom.left).map_id A.module)
  map_comp f g := SimplicialPseudoFamily.Pair.hom_ext (by
    simp only [SimplicialPseudoFamily.Pair.comp_map]
    exact (Scheme.Modules.pullback N.objectsIso.hom.left).map_comp f.hom g.hom)

/-- **Descent data give quasi-coherent pairs on the nerve.** -/
noncomputable def descentDataToPair : DescentData G ⥤ QuasicoherentZariskiPair N.toSchemes :=
  ObjectProperty.lift _ N.descentDataToPairFunctor (fun A =>
    have := A.isQuasicoherent
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _)

/-- The functor `descentDataToPairFunctor` is faithful. -/
instance : N.descentDataToPairFunctor.Faithful where
  map_injective {_ _} _ _ h := DescentData.Hom.ext
    ((Scheme.Modules.pullback N.objectsIso.hom.left).map_injective
      (congrArg SimplicialPseudoFamily.Pair.Hom.map h))

/-- The functor `descentDataToPairFunctor` is full. -/
instance : N.descentDataToPairFunctor.Full where
  map_surjective {A B} φ := by
    let ψ : (Scheme.Modules.pullback N.objectsIso.hom.left).obj A.module ⟶
        (Scheme.Modules.pullback N.objectsIso.hom.left).obj B.module := φ.map
    have hψ : (Scheme.Modules.pullback N.objectsIso.hom.left).map
        ((Scheme.Modules.pullback N.objectsIso.hom.left).preimage ψ) = ψ := Functor.map_preimage _ _
    refine ⟨⟨(Scheme.Modules.pullback N.objectsIso.hom.left).preimage ψ, ?_⟩,
      SimplicialPseudoFamily.Pair.hom_ext hψ⟩
    apply transportHom_injective N.face_one_one N.face_one_zero
    rw [transportHom_comp_map, map_comp_transportHom, hψ]
    exact φ.comm.symm

/-- The functor `descentDataToPair` is faithful. -/
instance : N.descentDataToPair.Faithful :=
  have : (N.descentDataToPair ⋙ ObjectProperty.ι _).Faithful :=
    (inferInstance : N.descentDataToPairFunctor.Faithful)
  Functor.Faithful.of_comp _ (ObjectProperty.ι _)

/-- The functor `descentDataToPair` is full. -/
instance : N.descentDataToPair.Full :=
  have : (N.descentDataToPair ⋙ ObjectProperty.ι _).Full :=
    (inferInstance : N.descentDataToPairFunctor.Full)
  Functor.Full.of_comp_faithful _ (ObjectProperty.ι _)

section EssSurj

variable {N} (A : (zariskiModuleFamily N.toSchemes).Pair)

/-- The module on the object scheme underlying a pair on the nerve: the pullback of its module
along the inverse of the identification of the degree-zero part with the object scheme. -/
noncomputable def pairModule : G.objects.left.Modules :=
  (Scheme.Modules.pullback (inv N.objectsIso.hom.left)).obj A.obj

/-- The pullback of `pairModule A` to the degree-zero part of the nerve is the module of `A`. -/
noncomputable def pairModuleIso :
    (Scheme.Modules.pullback N.objectsIso.hom.left).obj (pairModule A) ≅ A.obj :=
  (Scheme.Modules.pullbackComp N.objectsIso.hom.left (inv N.objectsIso.hom.left)).app A.obj ≪≫
    (Scheme.Modules.pullbackCongr (IsIso.hom_inv_id N.objectsIso.hom.left)).app A.obj ≪≫
      (Scheme.Modules.pullbackId _).app A.obj

/-- The comparison isomorphism of a pair, conjugated to the pullback of `pairModule A`. -/
noncomputable def pairConjIso :
    ((zariskiModuleFamily N.toSchemes).map (SimplexCategory.δ (1 : Fin 2))).obj
        ((Scheme.Modules.pullback N.objectsIso.hom.left).obj (pairModule A)) ≅
      ((zariskiModuleFamily N.toSchemes).map (SimplexCategory.δ (0 : Fin 2))).obj
        ((Scheme.Modules.pullback N.objectsIso.hom.left).obj (pairModule A)) :=
  ((zariskiModuleFamily N.toSchemes).map (SimplexCategory.δ (1 : Fin 2))).mapIso
      (pairModuleIso A) ≪≫ A.iso ≪≫
    ((zariskiModuleFamily N.toSchemes).map (SimplexCategory.δ (0 : Fin 2))).mapIso
      (pairModuleIso A).symm

/-- The descent morphism of a pair on the nerve. -/
noncomputable def pairAlpha :
    (Scheme.Modules.pullback G.target.left).obj (pairModule A) ⟶
      (Scheme.Modules.pullback G.source.left).obj (pairModule A) :=
  transportPreimage N.face_one_one N.face_one_zero (pairConjIso A).hom

/-- Transporting `pairAlpha A` to the faces of degree one of the nerve gives `pairConjIso A`. -/
theorem transportHom_pairAlpha :
    transportHom N.face_one_one N.face_one_zero (pairAlpha A) = (pairConjIso A).hom :=
  transportHom_transportPreimage N.face_one_one N.face_one_zero _

/-- The descent morphism `pairAlpha A` is an isomorphism. -/
instance : IsIso (pairAlpha A) := by
  have : IsIso (transportHom N.face_one_one N.face_one_zero (pairAlpha A)) := by
    rw [transportHom_pairAlpha]
    infer_instance
  exact isIso_of_isIso_transportHom N.face_one_one N.face_one_zero _

/-- The descent morphism `pairAlpha A` satisfies the cocycle condition on the scheme of
composable arrows. -/
theorem pairAlpha_cocycle :
    successiveDescent G (pairAlpha A) = reindexHom G.comp.left (pairAlpha A) := by
  refine (N.isCocycle_asIso_transportHom_iff (pairAlpha A)).1 ?_
  rw [show asIso (transportHom N.face_one_one N.face_one_zero (pairAlpha A)) = pairConjIso A from
    Iso.ext (transportHom_pairAlpha A)]
  unfold pairConjIso
  exact SimplicialPseudoFamily.isCocycle_conj (P := zariskiModuleFamily N.toSchemes) (F := A.obj)
    (F' := (Scheme.Modules.pullback N.objectsIso.hom.left).obj (pairModule A)) (pairModuleIso A)
    A.cocycle

/-- The descent datum of a pair on the nerve with quasi-coherent module. -/
noncomputable def pairDescentData (A : QuasicoherentZariskiPair N.toSchemes) : DescentData G where
  module := pairModule A.obj
  isQuasicoherent :=
    have := A.property
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _
  alpha := pairAlpha A.obj
  isIso_alpha := inferInstance
  cocycle := pairAlpha_cocycle A.obj

/-- The pair of the descent datum of a pair is that pair. -/
noncomputable def descentDataToPairPairDescentDataIso (A : QuasicoherentZariskiPair N.toSchemes) :
    N.descentDataToPair.obj (pairDescentData A) ≅ A :=
  ObjectProperty.isoMk _ (SimplicialPseudoFamily.Pair.isoMk (pairModuleIso A.obj) (by
    change _ = transportHom N.face_one_one N.face_one_zero (pairAlpha A.obj) ≫ _
    rw [transportHom_pairAlpha]
    have key : ∀ {𝒞 : Type (u + 1)} [Category.{u} 𝒞] {a b c d : 𝒞} (f : a ⟶ b) (g : b ⟶ c)
        (e : d ≅ c), f ≫ g = (f ≫ g ≫ e.inv) ≫ e.hom := by
      intros
      simp
    exact key _ _ (((zariskiModuleFamily N.toSchemes).map (SimplexCategory.δ (0 : Fin 2))).mapIso
      (pairModuleIso A.obj))))

end EssSurj

/-- The functor `descentDataToPair` is essentially surjective. -/
instance : N.descentDataToPair.EssSurj where
  mem_essImage A := ⟨pairDescentData A, ⟨descentDataToPairPairDescentDataIso A⟩⟩

/-- The functor `descentDataToPair` is an equivalence of categories. -/
instance : N.descentDataToPair.IsEquivalence := { }

/-- **Descent data on a groupoid scheme are the quasi-coherent pairs on its nerve.** -/
noncomputable def descentDataEquivPair : DescentData G ≌ QuasicoherentZariskiPair N.toSchemes :=
  N.descentDataToPair.asEquivalence

/-- **The quasi-coherent modules on a groupoid scheme are the quasi-coherent modules on the total
Zariski site of its nerve**, for any simplicial scheme with the identifications of Stacks 07TN. -/
noncomputable def quasicoherentModuleEquiv :
    QuasicoherentModule G ≌ QuasicoherentZariskiModule N.toSchemes :=
  (descentDataEquivQuasicoherentModule G).symm.trans
    (N.descentDataEquivPair.trans (quasicoherentEquivQuasicoherentPair N.toSchemes).symm)

end GroupoidSimplicialScheme

/-- **Stacks 07TP.**  Let `S` be a scheme, `(U,R,s,t,c)` a groupoid scheme over `S` and `X` the
simplicial scheme of Stacks 07TN.  The category of quasi-coherent modules on `(U,R,s,t,c)` in
the sense of Stacks 03LI is equivalent to the category of quasi-coherent modules on `X_{Zar}`.

The equivalence is the composite of three steps.  Quasi-coherent modules on the total Zariski
site are the pairs `(ℱ, α)` of Stacks 07TH with quasi-coherent degree-zero module, by Stacks 07TH
and Stacks 0D7M; such pairs are the groupoid descent data of `(U,R,s,t,c)`, because in degrees
`≤ 2` the nerve is `U`, `R` and `R ×_{s,U,t} R` with faces the source, the target, the two
projections and the composition law; and groupoid descent data are the quasi-coherent modules of
Stacks 03LI, which is `descentDataEquivQuasicoherentModule`. -/
@[stacks 07TP "The normalization `e^*α = id` of Stacks 03LI, which the source's proof passes \
over, is proved here: it is automatic for an invertible descent morphism satisfying the cocycle \
condition."]
noncomputable def quasicoherentModuleEquivQuasicoherentOnTotalSite :
    QuasicoherentModule G ≌ QuasicoherentZariskiModule (groupoidSimplicialScheme G).toSchemes :=
  (groupoidSimplicialScheme G).quasicoherentModuleEquiv

end TotalSite

end GroupoidScheme

end Stacks.Groupoids

end
