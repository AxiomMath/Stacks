module

public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# The meet of two subobjects, and the second isomorphism theorem

The last paragraph of the proof of [Stacks, Tag 01YH] runs the following argument. Given two
nonzero quasi-coherent sheaves of ideals `I` and `I'` on an integral scheme, it forms the
intersection `I'' = I ⊓ I'` and reads off the two short exact sequences

`0 → i_* I'' → i_* I  → Q  → 0` and `0 → i_* I'' → i_* I' → Q' → 0`

whose quotients `Q` and `Q'` are supported strictly inside the closed set. The *only* input the
argument needs about the intersection is that each quotient embeds into the quotient by the
*other* ideal: `I / (I ⊓ I') ↪ 𝒪 / I'` and `I' / (I ⊓ I') ↪ 𝒪 / I`. That is the second
isomorphism theorem, and it holds in any abelian category — no sheaf, scheme or ideal is
involved.

This file isolates it. The meet of two subobjects `a : A ⟶ D` and `b : B ⟶ D` is realized as
the kernel of `a ≫ cokernel.π b`, which makes `A / (A ⊓ B)` *definitionally* the Mathlib
coimage `CategoryTheory.Abelian.coimage (a ≫ cokernel.π b)`, so the monomorphism into
`cokernel b` is `CategoryTheory.Abelian.factorThruCoimage` and needs no proof at all. The
symmetric statement is obtained from an isomorphism `meet a b ≅ meet b a` rather than by
repeating the construction.

## Main definitions

* `meet`: the meet of two subobjects of a common object, as the kernel of the composite with the
  cokernel projection of the second.
* `meetFst`, `meetSnd`: its two monomorphisms into `A` and into `B`.
* `meetSymm`: the commutativity isomorphism `meet a b ≅ meet b a`.

## Main results

* `meetFstCokernelHom` and `mono_meetFstCokernelHom`: the monomorphism
  `cokernel (meetFst a b) ⟶ cokernel b`, i.e. `A / (A ⊓ B) ↪ D / B`.
* `meetSndCokernelHom` and `mono_meetSndCokernelHom`: the monomorphism
  `cokernel (meetSnd a b) ⟶ cokernel a`, i.e. `B / (A ⊓ B) ↪ D / A`.

## Implementation notes

`meetSnd` is built with `CategoryTheory.Abelian.monoLift`, which is the only place monicity of
`b` is used: the composite `meet a b ⟶ A ⟶ D` kills `cokernel.π b`, hence factors through `b`.

`cokernelIsoOfIsoComp` takes its mediating equation as an explicit hypothesis. It is stated in
the direction `e.inv ≫ f = g` because that is the form `meetSymmHom_comp_meetSnd` supplies, with
`(meetSymm a b).inv` reducing to `meetSymmHom b a`; stating it as `e.hom ≫ g = f` would make the
rewrite of `g` inside `cokernel.π g` fire and produce an unprovable goal.

## References

* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Stacks.AlgebraicGeometry.Tag01YHTopIdeals

variable {C : Type u} [Category.{v} C] [Abelian C] {A B D : C}

/-! ### Cokernels along an isomorphism of sources -/

section CokernelIso

variable {W W' T : C} (e : W ≅ W') (f : W ⟶ T) (g : W' ⟶ T)

/-- The forward map of `cokernelIsoOfIsoComp`. -/
def cokernelCompHom (h : e.inv ≫ f = g) : cokernel f ⟶ cokernel g :=
  cokernel.desc f (cokernel.π g) (by
    have hf : f = e.hom ≫ g := by rw [← h, Iso.hom_inv_id_assoc]
    rw [hf, Category.assoc, cokernel.condition, comp_zero])

/-- The backward map of `cokernelIsoOfIsoComp`. -/
def cokernelCompInv (h : e.inv ≫ f = g) : cokernel g ⟶ cokernel f :=
  cokernel.desc g (cokernel.π f) (by
    rw [← h, Category.assoc, cokernel.condition, comp_zero])

/-- **Two arrows into the same object whose sources are isomorphic over that object have
isomorphic cokernels.** -/
def cokernelIsoOfIsoComp (h : e.inv ≫ f = g) : cokernel f ≅ cokernel g where
  hom := cokernelCompHom e f g h
  inv := cokernelCompInv e f g h
  hom_inv_id := by
    refine coequalizer.hom_ext ?_
    simp only [cokernelCompHom, cokernelCompInv]
    rw [← Category.assoc, cokernel.π_desc, cokernel.π_desc, Category.comp_id]
  inv_hom_id := by
    refine coequalizer.hom_ext ?_
    simp only [cokernelCompHom, cokernelCompInv]
    rw [← Category.assoc, cokernel.π_desc, cokernel.π_desc, Category.comp_id]

end CokernelIso

/-! ### The meet of two subobjects -/

/-- **The meet of two subobjects of `D`**, realized as the kernel of the composite of the first
with the cokernel projection of the second. For `a` and `b` monomorphisms this is the
intersection `A ∩ B` inside `D`. -/
def meet (a : A ⟶ D) (b : B ⟶ D) : C := kernel (a ≫ cokernel.π b)

/-- The projection of the meet to its first factor. -/
def meetFst (a : A ⟶ D) (b : B ⟶ D) : meet a b ⟶ A := kernel.ι (a ≫ cokernel.π b)

/-- The projection `meetFst a b` is a monomorphism. -/
instance mono_meetFst (a : A ⟶ D) (b : B ⟶ D) : Mono (meetFst a b) :=
  inferInstanceAs (Mono (kernel.ι (a ≫ cokernel.π b)))

/-- The composite `meet a b ⟶ A ⟶ D ⟶ cokernel b` is zero. -/
theorem meetFst_comp_comp (a : A ⟶ D) (b : B ⟶ D) :
    meetFst a b ≫ a ≫ cokernel.π b = 0 := kernel.condition (a ≫ cokernel.π b)

/-- The projection of the meet to its second factor: the factorization of `meetFst a b ≫ a`
through the monomorphism `b`. -/
def meetSnd (a : A ⟶ D) (b : B ⟶ D) [Mono b] : meet a b ⟶ B :=
  Abelian.monoLift b (meetFst a b ≫ a) (by rw [Category.assoc]; exact meetFst_comp_comp a b)

/-- The two projections of the meet agree after composing into `D`. -/
theorem meetSnd_comp (a : A ⟶ D) (b : B ⟶ D) [Mono b] :
    meetSnd a b ≫ b = meetFst a b ≫ a :=
  Abelian.monoLift_comp b (meetFst a b ≫ a) _

/-- For `a` and `b` monomorphisms, the projection `meetSnd a b` is a monomorphism. -/
instance mono_meetSnd (a : A ⟶ D) (b : B ⟶ D) [Mono a] [Mono b] : Mono (meetSnd a b) :=
  mono_of_mono_fac (h := meetFst a b ≫ a) (meetSnd_comp a b)

/-! ### The second isomorphism theorem -/

/-- **`A / (A ⊓ B) ↪ D / B`.** The meet is by construction the kernel of
`a ≫ cokernel.π b`, so this quotient is the Mathlib coimage of that arrow and the embedding is
`CategoryTheory.Abelian.factorThruCoimage`. -/
def meetFstCokernelHom (a : A ⟶ D) (b : B ⟶ D) : cokernel (meetFst a b) ⟶ cokernel b :=
  Abelian.factorThruCoimage (a ≫ cokernel.π b)

/-- The map `meetFstCokernelHom a b : A / (A ⊓ B) ⟶ D / B` is a monomorphism. -/
instance mono_meetFstCokernelHom (a : A ⟶ D) (b : B ⟶ D) : Mono (meetFstCokernelHom a b) :=
  inferInstanceAs (Mono (Abelian.factorThruCoimage (a ≫ cokernel.π b)))

/-! ### Commutativity of the meet -/

/-- The meet of `a` and `b` maps to the meet of `b` and `a`. -/
def meetSymmHom (a : A ⟶ D) (b : B ⟶ D) [Mono a] [Mono b] : meet a b ⟶ meet b a :=
  kernel.lift (b ≫ cokernel.π a) (meetSnd a b) (by
    rw [← Category.assoc, meetSnd_comp, Category.assoc, cokernel.condition, comp_zero])

/-- Composing `meetSymmHom a b` with the first projection of `meet b a` gives the second
projection of `meet a b`. -/
theorem meetSymmHom_comp_meetFst (a : A ⟶ D) (b : B ⟶ D) [Mono a] [Mono b] :
    meetSymmHom a b ≫ meetFst b a = meetSnd a b :=
  kernel.lift_ι (b ≫ cokernel.π a) (meetSnd a b) _

/-- Composing `meetSymmHom a b` with the second projection of `meet b a` gives the first
projection of `meet a b`. -/
theorem meetSymmHom_comp_meetSnd (a : A ⟶ D) (b : B ⟶ D) [Mono a] [Mono b] :
    meetSymmHom a b ≫ meetSnd b a = meetFst a b := by
  rw [← cancel_mono a, Category.assoc, meetSnd_comp b a, ← Category.assoc,
    meetSymmHom_comp_meetFst, meetSnd_comp]

/-- **The meet is commutative.** -/
def meetSymm (a : A ⟶ D) (b : B ⟶ D) [Mono a] [Mono b] : meet a b ≅ meet b a where
  hom := meetSymmHom a b
  inv := meetSymmHom b a
  hom_inv_id := by
    rw [← cancel_mono (meetFst a b), Category.id_comp, Category.assoc,
      meetSymmHom_comp_meetFst, meetSymmHom_comp_meetSnd]
  inv_hom_id := by
    rw [← cancel_mono (meetFst b a), Category.id_comp, Category.assoc,
      meetSymmHom_comp_meetFst, meetSymmHom_comp_meetSnd]

/-- **`B / (A ⊓ B) ↪ D / A`**, the statement of `meetFstCokernelHom` with the two subobjects
exchanged, transported along `meetSymm`. -/
def meetSndCokernelHom (a : A ⟶ D) (b : B ⟶ D) [Mono a] [Mono b] :
    cokernel (meetSnd a b) ⟶ cokernel a :=
  (cokernelIsoOfIsoComp (meetSymm a b) (meetSnd a b) (meetFst b a)
    (meetSymmHom_comp_meetSnd b a)).hom ≫ meetFstCokernelHom b a

/-- The map `meetSndCokernelHom a b : B / (A ⊓ B) ⟶ D / A` is a monomorphism. -/
instance mono_meetSndCokernelHom (a : A ⟶ D) (b : B ⟶ D) [Mono a] [Mono b] :
    Mono (meetSndCokernelHom a b) := by
  unfold meetSndCokernelHom
  infer_instance

end Stacks.AlgebraicGeometry.Tag01YHTopIdeals

end
