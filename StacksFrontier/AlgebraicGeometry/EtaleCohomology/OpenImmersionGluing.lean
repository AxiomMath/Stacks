module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.Basic

/-!
# Gluing sections of an étale sheaf along open immersions

Let `G` be a sheaf of sets on the small étale site of a scheme `X`, let `T` be an object of that
site, and let `P a ⟶ T` be a family of morphisms whose underlying morphisms of schemes are open
immersions covering `T`. If for every two members the overlap of their images is covered by the
image of an object `Q a b` mapping to both compatibly, then the sections of `G` over `T` are the
equalizer of the sections over the `P a` and the `Q a b`.

Since open immersions are monomorphisms, a morphism into `P a` is determined by its composite with
`P a ⟶ T`, so only the composites into `T` need to be compared. This is the Zariski gluing step
that passes from affine pieces to a quasi-compact scheme.

## Main results

* `Stacks.EtaleCohomology.hom_ext_of_mono_left`: morphisms into `P` are determined by their
  composite with a morphism out of `P` whose underlying morphism is a monomorphism.
* `Stacks.EtaleCohomology.etaleSheaf_sep_of_openImmersion`,
  `Stacks.EtaleCohomology.etaleSheaf_glue_of_openImmersion`: the equalizer property.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

namespace Stacks.EtaleCohomology

/-- Precomposing with an isomorphism does not change the image of a morphism. -/
private theorem range_comp_base_of_isIso {A B C : Scheme.{u}} (e : A ⟶ B) [IsIso e] (g : B ⟶ C) :
    Set.range (e ≫ g).base = Set.range g.base := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr (ConcreteCategory.bijective_of_isIso e.base).2, Set.image_univ]

/-- The image of the base change of an open immersion is the preimage of its image. -/
theorem mem_range_snd_iff_of_isPullback {P A B C : Scheme.{u}} {fst : P ⟶ A} {snd : P ⟶ B}
    {f : A ⟶ C} {g : B ⟶ C} [IsOpenImmersion f] (h : IsPullback fst snd f g) (b : B) :
    b ∈ Set.range snd.base ↔ g.base b ∈ Set.range f.base := by
  have e : Set.range snd.base = Set.range (pullback.snd f g).base := by
    rw [← h.isoPullback_hom_snd, range_comp_base_of_isIso]
  rw [e, IsOpenImmersion.range_pullbackSnd]
  rfl

/-- **A quasi-compact open is covered by finitely many affine opens contained in it.** -/
theorem exists_finite_affine_cover {Z : Scheme.{u}} (W : Z.Opens) (hW : IsCompact (W : Set Z)) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → Z.Opens), (∀ m, IsAffineOpen (V m)) ∧ (∀ m, V m ≤ W) ∧
      (W : Set Z) ⊆ ⋃ m, (V m : Set Z) := by
  classical
  have hpt : ∀ x : W, ∃ V : Z.Opens, IsAffineOpen V ∧ (x : Z) ∈ V ∧ V ≤ W := by
    intro x
    obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open x.2 W.isOpen
    exact ⟨V, hV, hxV, hVW⟩
  choose V hVaff hxV hVW using hpt
  obtain ⟨t, ht⟩ := hW.elim_finite_subcover (fun x : W => (V x : Set Z)) (fun x => (V x).isOpen)
    fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  refine ⟨{x : W // x ∈ t}, inferInstance, fun m => V m.1, fun m => hVaff _, fun m => hVW _, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
  exact Set.mem_iUnion.2 ⟨⟨y, hy⟩, hxy⟩

variable {X : Scheme.{u}}

/-- The underlying morphism of a morphism of a small étale site is étale. -/
theorem etale_left {A A' : X.Etale} (f : A ⟶ A') : Etale f.left := by
  have hw : f.left ≫ A'.hom = A.hom := MorphismProperty.Over.w f
  have hA : Etale A.hom := A.prop
  have : Etale (f.left ≫ A'.hom) := by rw [hw]; exact hA
  exact Etale.of_comp f.left A'.hom

/-- The underlying morphism of an isomorphism of a small étale site is an isomorphism. -/
theorem etale_isIso_left {A A' : X.Etale} (e : A ≅ A') : IsIso e.hom.left :=
  ⟨⟨e.inv.left, congrArg (fun m => m.left) e.hom_inv_id, congrArg (fun m => m.left) e.inv_hom_id⟩⟩

/-- Being an open immersion over `X` is invariant under isomorphism in the small étale site. -/
theorem isOpenImmersion_hom_of_iso {A A' : X.Etale} (e : A ≅ A') (h : IsOpenImmersion A'.hom) :
    IsOpenImmersion A.hom := by
  have hw : e.hom.left ≫ A'.hom = A.hom := MorphismProperty.Over.w e.hom
  have := etale_isIso_left e
  rw [← hw]
  infer_instance

/-- Isomorphic objects of the small étale site have the same image in `X`. -/
theorem range_hom_of_iso {A A' : X.Etale} (e : A ≅ A') :
    Set.range A.hom.base = Set.range A'.hom.base := by
  have hw : e.hom.left ≫ A'.hom = A.hom := MorphismProperty.Over.w e.hom
  have := etale_isIso_left e
  rw [← hw, range_comp_base_of_isIso]

/-- A morphism of the small étale site lies over the base, on points. -/
theorem etale_hom_base_apply {W V : X.Etale} (f : W ⟶ V) (w : W.left) :
    V.hom.base (f.left.base w) = W.hom.base w := by
  have hw : f.left ≫ V.hom = W.hom := MorphismProperty.Over.w f
  rw [← hw, Scheme.Hom.comp_apply]

/-- Two morphisms into `P` agreeing after a morphism `P ⟶ V` whose underlying morphism of schemes
is a monomorphism are equal. -/
theorem hom_ext_of_mono_left {W P V : X.Etale} (p : P ⟶ V) [Mono p.left] (f g : W ⟶ P)
    (h : f ≫ p = g ≫ p) : f = g :=
  MorphismProperty.Over.Hom.ext ((cancel_mono p.left).1 (congrArg (fun m => m.left) h))

variable (G : Sheaf X.smallEtaleTopology (Type w)) {T : X.Etale}
  {A : Type*} (P : A → X.Etale) (p : ∀ a, P a ⟶ T) [∀ a, IsOpenImmersion (p a).left]
  (hcov : ∀ t : T.left, ∃ a, t ∈ Set.range (p a).left.base)

include hcov in
omit [∀ (a : A), IsOpenImmersion (p a).left] in
/-- A family of open immersions into `T` whose images cover `T` generates a covering sieve of the
small étale site. -/
theorem ofArrows_mem_of_openImmersion :
    Sieve.ofArrows P p ∈ X.smallEtaleTopology T := by
  rw [mem_smallEtaleTopology_iff]
  intro t
  obtain ⟨a, ha⟩ := hcov t
  exact ⟨P a, p a, Sieve.ofArrows_mk _ _ a, ha⟩

/-- The presieve generated by an open cover of `T` is a sheaf-for presieve for `G`. -/
private theorem isSheafFor_ofArrows_of_openImmersion (P : A → X.Etale) (p : ∀ a, P a ⟶ T)
    (hcov : ∀ t : T.left, ∃ a, t ∈ Set.range (p a).left.base) :
    (Presieve.ofArrows P p).IsSheafFor G.obj := by
  have hs := ((isSheaf_iff_isSheaf_of_type _ _).1 G.property) _
    (ofArrows_mem_of_openImmersion P p hcov)
  rwa [← Presieve.isSheafFor_iff_generate] at hs

include hcov in
omit [∀ (a : A), IsOpenImmersion (p a).left] in
/-- Sections over `T` agreeing on every member of an open cover are equal. -/
theorem etaleSheaf_sep_of_openImmersion (x y : G.obj.obj (op T))
    (h : ∀ a, G.obj.map (p a).op x = G.obj.map (p a).op y) : x = y := by
  refine (isSheafFor_ofArrows_of_openImmersion G P p hcov).isSeparatedFor.ext fun _ _ hf => ?_
  obtain ⟨a⟩ := hf
  exact h a

variable {O : Type*} (src tgt : O → A) (Q : O → X.Etale) (q₁ : ∀ o, Q o ⟶ P (src o))
  (q₂ : ∀ o, Q o ⟶ P (tgt o)) (hq : ∀ o, q₁ o ≫ p (src o) = q₂ o ≫ p (tgt o))
  (hQo : ∀ o, IsOpenImmersion (q₁ o ≫ p (src o)).left)
  (hQ : ∀ a b, Set.range (p a).left.base ∩ Set.range (p b).left.base ⊆
    ⋃ (o : O) (_ : src o = a ∧ tgt o = b), Set.range (q₁ o ≫ p (src o)).left.base)

include hcov hq hQo hQ in
/-- **Gluing along an open cover with covered overlaps.** A family of sections over the members of
the cover agreeing on the pieces covering the overlaps glues to a section over `T`. -/
theorem etaleSheaf_glue_of_openImmersion (z : ∀ a, G.obj.obj (op (P a)))
    (hz : ∀ o, G.obj.map (q₁ o).op (z (src o)) = G.obj.map (q₂ o).op (z (tgt o))) :
    ∃ x, ∀ a, G.obj.map (p a).op x = z a := by
  have hs := isSheafFor_ofArrows_of_openImmersion G P p hcov
  rw [Presieve.isSheafFor_arrows_iff] at hs
  refine (hs z fun a b V ga gb hab => ?_).exists
  -- the sieve of `V` of the morphisms through which `ga` factors through some overlap piece
  let S : Sieve V :=
    { arrows := fun V' f => ∃ (o : O) (h : src o = a ∧ tgt o = b) (l : V' ⟶ Q o),
        l ≫ q₁ o ≫ p (src o) = f ≫ ga ≫ p a
      downward_closed := by
        rintro V₁ V₂ f ⟨o, h, l, hl⟩ g
        exact ⟨o, h, g ≫ l, by rw [Category.assoc, hl, Category.assoc]⟩ }
  have hS : S ∈ X.smallEtaleTopology V := by
    rw [mem_smallEtaleTopology_iff]
    intro v
    obtain ⟨o', ho', hvo⟩ := Set.mem_iUnion₂.1 (hQ a b ⟨⟨ga.left.base v, rfl⟩,
      ⟨gb.left.base v, congrArg (fun m => m.left.base v) hab.symm⟩⟩)
    have := hQo o'
    let U : V.left.Opens := (ga ≫ p a).left ⁻¹ᵁ (q₁ o' ≫ p (src o')).left.opensRange
    have : Etale (U.ι ≫ V.hom) := inferInstance
    let V' : X.Etale := Scheme.Etale.mk (U.ι ≫ V.hom)
    let f : V' ⟶ V := MorphismProperty.Over.homMk U.ι rfl trivial
    have hr : Set.range (f ≫ ga ≫ p a).left.base ⊆ Set.range (q₁ o' ≫ p (src o')).left.base := by
      rintro _ ⟨w, rfl⟩
      exact w.2
    let l : V' ⟶ Q o' := MorphismProperty.Over.homMk
      (IsOpenImmersion.lift (q₁ o' ≫ p (src o')).left (f ≫ ga ≫ p a).left hr) (by
        have h1 := IsOpenImmersion.lift_fac (q₁ o' ≫ p (src o')).left (f ≫ ga ≫ p a).left hr
        have h2 : (q₁ o' ≫ p (src o')).left ≫ T.hom = (Q o').hom := MorphismProperty.Over.w _
        have h3 : (f ≫ ga ≫ p a).left ≫ T.hom = V'.hom := MorphismProperty.Over.w _
        exact (congrArg (_ ≫ ·) h2.symm).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ T.hom) h1).trans h3))) trivial
    refine ⟨V', f, ⟨o', ho', l, MorphismProperty.Over.Hom.ext (IsOpenImmersion.lift_fac _ _ _)⟩, ?_⟩
    exact ⟨⟨v, hvo⟩, rfl⟩
  have hsep := ((isSheaf_iff_isSheaf_of_type _ _).1 G.property) _ hS
  refine hsep.isSeparatedFor.ext fun V' f hf => ?_
  obtain ⟨o, ⟨rfl, rfl⟩, l, hl⟩ := hf
  have ea : f ≫ ga = l ≫ q₁ o := hom_ext_of_mono_left (p (src o)) _ _ (by
    rw [Category.assoc, Category.assoc]; exact hl.symm)
  have eb : f ≫ gb = l ≫ q₂ o := hom_ext_of_mono_left (p (tgt o)) _ _ (by
    rw [Category.assoc, Category.assoc, ← hq, ← hab]; exact hl.symm)
  change G.obj.map f.op (G.obj.map ga.op (z (src o))) = G.obj.map f.op (G.obj.map gb.op (z (tgt o)))
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp, ← op_comp, ← op_comp, ea, eb, op_comp, op_comp, Functor.map_comp,
    Functor.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  exact congrArg (G.obj.map l.op) (hz o)

end Stacks.EtaleCohomology
