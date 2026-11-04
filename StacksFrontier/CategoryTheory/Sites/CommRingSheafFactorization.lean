module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Factoring a map of sheaves of commutative rings through a locally surjective one

Let `q : A ⟶ B` be a locally surjective morphism of presheaves of commutative rings on a site
`(C, J)` and let `g : A ⟶ R` be a morphism into a presheaf whose underlying presheaf of sets is
a sheaf. If every local section killed by `q` is killed by `g`, then `g` factors uniquely
through `q`:

```
  A --q--> B
   \       ¦
    g      ∃! s
     \     v
      ---> R
```

This is the sheaf-theoretic form of "a ring map killing the kernel of a surjection descends to
the quotient". The value of the factorisation on a local section `b` of `B` is obtained by
lifting `b` through `q` on a covering sieve, applying `g`, and gluing in `R`; the hypothesis on
kernels is exactly what makes the resulting family of local sections compatible, and hence
independent of the lifts.

## Main results

* `Stacks.Sites.existsUnique_commRingFactor`: the factorisation exists and is unique.
* `Stacks.Sites.commRingHom_ext_of_isLocallySurjective`: a locally surjective morphism of
  presheaves of commutative rings can be cancelled on the left against two maps into a sheaf.
* `Stacks.Sites.isSheaf_comp_forget_commRingCat`: the presheaf of sets underlying a sheaf of
  commutative rings is a sheaf, on any site and for any universe of sections.

## Implementation notes

The statements are about *presheaves* of commutative rings together with an explicit hypothesis
that the target satisfies the sheaf condition for type-valued presheaves. That is the form in
which the hypothesis is used: only the sheaf condition on the target enters, and neither `A` nor
`B` need be a sheaf. For a `CategoryTheory.Sheaf` of commutative rings the hypothesis is
supplied by `Stacks.Sites.isSheaf_comp_forget_commRingCat`, which passes from
`CategoryTheory.Presheaf.IsSheaf` to the type-valued sheaf condition through
`CategoryTheory.GrothendieckTopology.HasSheafCompose` for `forget₂ CommRingCat RingCat` and for
`forget RingCat`, and so needs no size hypothesis relating the site to the universe of sections.

That the factorisation is a map of commutative rings, and not merely of sheaves of sets, is
proved from separatedness of the target: the two sides of each ring axiom agree after
restriction along every arrow of a covering sieve on which the arguments lift through `q`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks.Sites

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The presheaf of sets underlying a sheaf of commutative rings satisfies the sheaf condition
for type-valued presheaves. No size hypothesis relating the site to the universe of sections is
needed: the sheaf condition is preserved by `forget₂ CommRingCat RingCat` and then by
`forget RingCat`, whose composite is `forget CommRingCat`. -/
theorem isSheaf_comp_forget_commRingCat [J.HasSheafCompose (forget RingCat.{w})]
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {O : Cᵒᵖ ⥤ CommRingCat.{w}} (hO : Presheaf.IsSheaf J O) :
    Presieve.IsSheaf J (O ⋙ forget CommRingCat.{w}) := by
  have h1 : Presheaf.IsSheaf J (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}) :=
    GrothendieckTopology.HasSheafCompose.isSheaf O hO
  have h2 : Presheaf.IsSheaf J
      ((O ⋙ forget₂ CommRingCat.{w} RingCat.{w}) ⋙ forget RingCat.{w}) :=
    GrothendieckTopology.HasSheafCompose.isSheaf _ h1
  rw [Functor.assoc, HasForget₂.forget_comp, isSheaf_iff_isSheaf_of_type] at h2
  exact h2

section Factor

variable {A B R : Cᵒᵖ ⥤ CommRingCat.{w}} (q : A ⟶ B) (g : A ⟶ R)
  (hq : Presheaf.IsLocallySurjective J q)
  (hR : Presieve.IsSheaf J (R ⋙ forget CommRingCat.{w}))
  (hker : ∀ (U : Cᵒᵖ) (a : A.obj U), q.app U a = 0 → g.app U a = 0)

include hker in
/-- Two local sections with the same image under `q` have the same image under `g`. -/
private theorem eq_of_q_eq {U : Cᵒᵖ} {a a' : A.obj U} (h : q.app U a = q.app U a') :
    g.app U a = g.app U a' := by
  have h0 : q.app U (a - a') = 0 := by
    rw [map_sub, h, sub_self]
  have h1 := hker U (a - a') h0
  rw [map_sub, sub_eq_zero] at h1
  exact h1

include hq in
private theorem imageSieve_mem_of_section {U : Cᵒᵖ} (b : B.obj U) :
    Presheaf.imageSieve q b ∈ J U.unop :=
  have := hq
  Presheaf.imageSieve_mem J q b

/-- The family of local sections of `R` attached to a local section `b` of `B`: on an arrow
along which `b` lifts through `q`, the image under `g` of a chosen lift. -/
private noncomputable def liftFamily {U : Cᵒᵖ} (b : B.obj U) :
    Presieve.FamilyOfElements (R ⋙ forget CommRingCat.{w})
      (Presheaf.imageSieve q b).arrows :=
  fun _ p hp => g.app _ (Presheaf.localPreimage q b p hp)

include hker in
private theorem liftFamily_compatible {U : Cᵒᵖ} (b : B.obj U) :
    (liftFamily q g b).Compatible := by
  intro Y₁ Y₂ Z p₁ p₂ f₁ f₂ h₁ h₂ hcomm
  show R.map p₁.op (g.app _ (Presheaf.localPreimage q b f₁ h₁)) =
    R.map p₂.op (g.app _ (Presheaf.localPreimage q b f₂ h₂))
  rw [← NatTrans.naturality_apply g p₁.op, ← NatTrans.naturality_apply g p₂.op]
  refine eq_of_q_eq q g hker ?_
  rw [NatTrans.naturality_apply q p₁.op, NatTrans.naturality_apply q p₂.op,
    Presheaf.app_localPreimage, Presheaf.app_localPreimage,
    ← Functor.map_comp_apply, ← Functor.map_comp_apply,
    ← op_comp, ← op_comp, hcomm]

/-- The local section of `R` glued from the images under `g` of local lifts of `b` through
`q`. -/
private noncomputable def descend {U : Cᵒᵖ} (b : B.obj U) : R.obj U :=
  (hR _ (imageSieve_mem_of_section q hq b)).amalgamate (liftFamily q g b)
    (liftFamily_compatible q g hker b)

include hq hR hker in
/-- **The defining property of the glued section.** Whenever a local section `a` of `A` lifts the
restriction of `b` along `p`, the restriction of the glued section along `p` is the image of `a`
under `g`. -/
private theorem map_descend {U : Cᵒᵖ} (b : B.obj U) {V : C} (p : V ⟶ U.unop) (a : A.obj (op V))
    (ha : q.app (op V) a = B.map p.op b) :
    R.map p.op (descend q g hq hR hker b) = g.app (op V) a := by
  have hp : (Presheaf.imageSieve q b).arrows p := ⟨a, ha⟩
  have hglue := (hR _ (imageSieve_mem_of_section q hq b)).valid_glue
    (liftFamily_compatible q g hker b) p hp
  refine (hglue.trans ?_ : R.map p.op (descend q g hq hR hker b) = _)
  exact eq_of_q_eq q g hker ((Presheaf.app_localPreimage q b p hp).trans ha.symm)

include hq hR hker in
private theorem eq_of_locally_eq {U : Cᵒᵖ} {S : Sieve U.unop} (hS : S ∈ J U.unop)
    (x y : R.obj U)
    (h : ∀ ⦃V : C⦄ (p : V ⟶ U.unop), S.arrows p → R.map p.op x = R.map p.op y) : x = y :=
  ((hR S hS).isSeparatedFor).ext h

/-- Two local sections of `R` agree if their restrictions agree along every arrow where two given
local sections `b b'` of `B` lift through `q`, the glued sections of `b`, `b'` then being the
images of the lifts. -/
private theorem eq_of_locally_lift_two {U : Cᵒᵖ} (b b' : B.obj U) (x y : R.obj U)
    (h : ∀ (V : C) (p : V ⟶ U.unop) (a a' : A.obj (op V)), q.app (op V) a = B.map p.op b →
      q.app (op V) a' = B.map p.op b' →
      R.map p.op (descend q g hq hR hker b) = g.app (op V) a →
      R.map p.op (descend q g hq hR hker b') = g.app (op V) a' →
      R.map p.op x = R.map p.op y) : x = y := by
  refine eq_of_locally_eq q g hq hR hker
    (J.intersection_covering (imageSieve_mem_of_section q hq b)
      (imageSieve_mem_of_section q hq b')) _ _ fun V p hp => ?_
  obtain ⟨⟨a, ha⟩, ⟨a', ha'⟩⟩ := hp
  exact h V p a a' ha ha' (map_descend q g hq hR hker b p a ha)
    (map_descend q g hq hR hker b' p a' ha')

include hq hR hker in
private theorem descend_add {U : Cᵒᵖ} (b b' : B.obj U) :
    descend q g hq hR hker (b + b') =
      descend q g hq hR hker b + descend q g hq hR hker b' := by
  refine eq_of_locally_lift_two q g hq hR hker b b' _ _ fun V p a a' ha ha' hb hb' => ?_
  rw [map_add, hb, hb', map_descend q g hq hR hker (b + b') p (a + a')
    (by rw [map_add, ha, ha', ← map_add]), map_add]

include hq hR hker in
private theorem descend_mul {U : Cᵒᵖ} (b b' : B.obj U) :
    descend q g hq hR hker (b * b') =
      descend q g hq hR hker b * descend q g hq hR hker b' := by
  refine eq_of_locally_lift_two q g hq hR hker b b' _ _ fun V p a a' ha ha' hb hb' => ?_
  rw [map_mul, hb, hb', map_descend q g hq hR hker (b * b') p (a * a')
    (by rw [map_mul, ha, ha', ← map_mul]), map_mul]

include hq hR hker in
private theorem descend_zero {U : Cᵒᵖ} : descend q g hq hR hker (0 : B.obj U) = 0 := by
  refine eq_of_locally_eq q g hq hR hker (J.top_mem U.unop) _ _ fun V p _ => ?_
  rw [map_descend q g hq hR hker (0 : B.obj U) p 0 (by rw [map_zero, map_zero]), map_zero,
    map_zero]

include hq hR hker in
private theorem descend_one {U : Cᵒᵖ} : descend q g hq hR hker (1 : B.obj U) = 1 := by
  refine eq_of_locally_eq q g hq hR hker (J.top_mem U.unop) _ _ fun V p _ => ?_
  rw [map_descend q g hq hR hker (1 : B.obj U) p 1 (by rw [map_one, map_one]), map_one, map_one]

include hq hR hker in
private theorem descend_naturality {U V : Cᵒᵖ} (f : U ⟶ V) (b : B.obj U) :
    descend q g hq hR hker (B.map f b) = R.map f (descend q g hq hR hker b) := by
  refine eq_of_locally_eq q g hq hR hker
    (imageSieve_mem_of_section q hq (B.map f b)) _ _ fun W k hk => ?_
  obtain ⟨a, ha⟩ := hk
  rw [map_descend q g hq hR hker (B.map f b) k a ha, ← Functor.map_comp_apply]
  refine (map_descend q g hq hR hker b (k ≫ f.unop) a ?_).symm
  rw [ha, ← Functor.map_comp_apply, op_comp, Quiver.Hom.op_unop]

include hq hR hker in
/-- The factorisation of `g` through `q`. -/
private noncomputable def factor : B ⟶ R where
  app U := CommRingCat.ofHom
    { toFun := fun b => descend q g hq hR hker b
      map_one' := descend_one q g hq hR hker
      map_mul' := fun b b' => descend_mul q g hq hR hker b b'
      map_zero' := descend_zero q g hq hR hker
      map_add' := fun b b' => descend_add q g hq hR hker b b' }
  naturality U V f := by
    ext b
    exact descend_naturality q g hq hR hker f b

include hq hR hker in
private theorem comp_factor : q ≫ factor q g hq hR hker = g := by
  ext U a
  show descend q g hq hR hker (q.app U a) = g.app U a
  refine eq_of_locally_eq q g hq hR hker
    (imageSieve_mem_of_section q hq (q.app U a)) _ _ fun V p _ => ?_
  rw [map_descend q g hq hR hker (q.app U a) p (A.map p.op a)
      (by rw [NatTrans.naturality_apply]), NatTrans.naturality_apply]

include hq hR hker in
/-- **A morphism of presheaves of commutative rings killing the kernel of a locally surjective
one factors uniquely through it.** -/
theorem existsUnique_commRingFactor : ∃! s : B ⟶ R, q ≫ s = g := by
  refine ⟨factor q g hq hR hker, comp_factor q g hq hR hker, fun s hs => ?_⟩
  ext U b
  refine eq_of_locally_eq q g hq hR hker (imageSieve_mem_of_section q hq b) _ _ fun V p hp => ?_
  obtain ⟨a, ha⟩ := hp
  rw [← NatTrans.naturality_apply s p.op, ← ha]
  have hsa : s.app (op V) (q.app (op V) a) = g.app (op V) a :=
    congrArg (fun m : A ⟶ R => m.app (op V) a) hs
  rw [hsa]
  exact (map_descend q g hq hR hker b p a ha).symm

end Factor

/-- **A locally surjective morphism of presheaves of commutative rings can be cancelled on the
left** against two morphisms into a presheaf whose underlying presheaf of sets is a sheaf. -/
theorem commRingHom_ext_of_isLocallySurjective {A B R : Cᵒᵖ ⥤ CommRingCat.{w}} (q : A ⟶ B)
    (hq : Presheaf.IsLocallySurjective J q)
    (hR : Presieve.IsSheaf J (R ⋙ forget CommRingCat.{w})) {s₁ s₂ : B ⟶ R}
    (h : q ≫ s₁ = q ≫ s₂) : s₁ = s₂ := by
  have hker : ∀ (U : Cᵒᵖ) (a : A.obj U), q.app U a = 0 → (q ≫ s₁).app U a = 0 := by
    intro U a ha
    show s₁.app U (q.app U a) = 0
    rw [ha, map_zero]
  obtain ⟨_, _, huniq⟩ := existsUnique_commRingFactor q (q ≫ s₁) hq hR hker
  exact (huniq s₁ rfl).trans (huniq s₂ h.symm).symm

end Stacks.Sites

end
