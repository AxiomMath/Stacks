module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.Envelope
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeRetract

/-!
# Divided power envelopes across a change of base and of target

The universal property of the divided power envelope of [Stacks, Tag 07H8],
`Crystalline.DividedPowerEnvelope.homEquiv`, is stated for a divided power ring `A`, a ring `B`
and an ideal `J ⊆ B`.  It therefore already allows the *target* of the envelope's universal map to
be an arbitrary divided power ring over `A`, and in particular another envelope — over another
base and for another ideal in another ring.

This file draws that consequence.  Given envelopes `D` of `J ⊆ B` over `(A, I, γ)` and `D'` of
`J' ⊆ B'` over `(A', I', γ')`, a divided power morphism `a : A → A'` of the bases and a ring map
`g : B → B'` which carries `J` into `J'` and is compatible with `a`, there is a divided power
morphism `D → D'` over `a`, unique with its restriction to `B`.  That is
`Crystalline.envelopePairMap`, and it is functorial.

The point of stating it is that `Crystalline.polynomialEnvelopeMap` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/Envelope.lean` maps the envelope of one
polynomial presentation of `s.C` to that of another presentation of the *same* `s.C`, for one
`Crystalline.AffineCrystallineSituation s`.  The system of [Stacks, Tag 07MM] needs instead a map
between the envelopes of presentations of the rings `C_α = Γ(U_α)` of two different Čech
intersections, which are the targets of two different situations.
`Crystalline.polynomialEnvelopeMapOver` is that map, over a morphism of situations
(`Crystalline.AffineCrystallineSituation.Hom`), and
`Crystalline.polynomialEnvelopeMapOver_eq_polynomialEnvelopeMap` says it restricts to the old one.

## Main definitions

* `Crystalline.AffineCrystallineSituation.Hom` — **a morphism of affine crystalline situations**:
  a divided power morphism of the divided power bases and a ring map of the targets, compatible.
* `Crystalline.envelopePairMap` — **the divided power morphism `D → D'` of envelopes** induced by
  a morphism of the two ring--ideal pairs over a morphism of the bases.
* `Crystalline.envelopeIdealMap` — its special case over a fixed base, which is the shape the
  Čech transitions of [Stacks, Tag 07MM] use.
* `Crystalline.polynomialEnvelopeMapOver` — `Crystalline.polynomialEnvelopeMap` across a morphism
  of affine crystalline situations.

## Main results

* `Crystalline.envelopePairMap_algebraMap` — the induced morphism agrees with `g` on the image
  of `B`, which with `Crystalline.envelopeHom_ext` determines it.
* `Crystalline.envelopePairMap_id` and `Crystalline.envelopePairMap_comp` —
  **functoriality**, by `Crystalline.eq_envelopePairMap`, the uniqueness half of the universal
  property in the form every use takes.
* `Crystalline.polynomialEnvelopeMapOver_eq_polynomialEnvelopeMap` — over the identity morphism
  of one situation the construction is the existing `Crystalline.polynomialEnvelopeMap`.

## What is and is not proved

Nothing here is new mathematics and **no tag attribute is placed**: every statement is an
instance of the universal property [Stacks, Tag 07H8], whose tag sits on
`Crystalline.dividedPowerEnvelope`, read with a target that the existing wrappers happened not to
allow.  In particular nothing about completions appears: these are the *uncompleted* envelopes.

## References

* [Stacks Project, Tag 07H8](https://stacks.math.columbia.edu/tag/07H8)
* [Stacks Project, Tag 07MD](https://stacks.math.columbia.edu/tag/07MD)
* [Stacks Project, Tag 07MM](https://stacks.math.columbia.edu/tag/07MM)
-/

@[expose] public section

namespace Crystalline

universe u v w

/-! ### Morphisms of affine crystalline situations -/

/-- **A morphism of the affine crystalline situations of [Stacks, Tag 07MD]**: a divided power
morphism `(A, I, γ) → (A', I', γ')` of the divided power bases together with a ring map
`C → C'` of the targets commuting with the two structural maps.

The situations of [Stacks, Tag 07MM] at two Čech intersections `U_α ⊆ U_{α ∘ φ}` are related by
such a morphism whose base part is the identity and whose target part is the restriction
`Γ(U_{α ∘ φ}) → Γ(U_α)`. -/
structure AffineCrystallineSituation.Hom (s t : AffineCrystallineSituation.{u, v}) where
  /-- The divided power morphism of the divided power bases. -/
  base : DividedPowers.DPMorphism s.A.dividedPowers t.A.dividedPowers
  /-- The ring map of the targets. -/
  target : s.C →+* t.C
  /-- The square of structural maps commutes. -/
  commutes : target.comp (algebraMap s.A s.C) = (algebraMap t.A t.C).comp base.toRingHom

namespace AffineCrystallineSituation.Hom

/-- The identity morphism of an affine crystalline situation. -/
def id (s : AffineCrystallineSituation.{u, v}) : AffineCrystallineSituation.Hom s s where
  base := DividedPowers.DPMorphism.id s.A.dividedPowers
  target := RingHom.id s.C
  commutes := rfl

/-- The composite of two morphisms of affine crystalline situations. -/
def comp {s t r : AffineCrystallineSituation.{u, v}}
    (σ : AffineCrystallineSituation.Hom t r) (τ : AffineCrystallineSituation.Hom s t) :
    AffineCrystallineSituation.Hom s r where
  base := σ.base.comp τ.base
  target := σ.target.comp τ.target
  commutes := RingHom.ext fun a =>
    (congrArg σ.target (RingHom.congr_fun τ.commutes a)).trans (RingHom.congr_fun σ.commutes _)

end AffineCrystallineSituation.Hom

/-! ### The envelope of a ring--ideal pair is functorial in the pair and the base -/

section PairMap

/-- Composing a divided power morphism with the identity on its source changes nothing. -/
private theorem dpMorphism_comp_id {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A}
    {J : Ideal B} {hI : DividedPowers I} {hJ : DividedPowers J}
    (φ : DividedPowers.DPMorphism hI hJ) :
    φ.comp (DividedPowers.DPMorphism.id hI) = φ :=
  rfl

variable {A A' A'' : DividedPowerRing.{u}} {B B' B'' : Type v}
  [CommRing B] [CommRing B'] [CommRing B'']
  {f : A →+* B} {J : Ideal B} {hJ : A.ideal.map f ≤ J}
  {f' : A' →+* B'} {J' : Ideal B'} {hJ' : A'.ideal.map f' ≤ J'}
  {f'' : A'' →+* B''} {J'' : Ideal B''} {hJ'' : A''.ideal.map f'' ≤ J''}

/-- The datum which the universal property of the envelope of `J` turns into a divided power
morphism into the envelope of `J'`: the canonical map of `(B', J')` into that envelope, composed
with the given map of ring--ideal pairs. -/
def envelopePairHomOver (D' : DividedPowerEnvelope A' f' J' hJ')
    (a : DividedPowers.DPMorphism A.dividedPowers A'.dividedPowers)
    (g : B →+* B') (hgJ : J.map g ≤ J') (hga : g.comp f = f'.comp a.toRingHom) :
    IdealPair.HomOver (IdealPair.Hom.ofRingHom f hJ)
      (IdealPair.Hom.ofDPMorphism (D'.structureMap.comp a)) :=
  ⟨IdealPair.Hom.comp D'.algebraMap (IdealPair.Hom.ofRingHom g hgJ), by
    apply IdealPair.Hom.ext_toRingHom
    change (D'.algebraMap.toRingHom.comp g).comp f = D'.structureMap.toRingHom.comp a.toRingHom
    rw [RingHom.comp_assoc, hga, ← RingHom.comp_assoc, D'.algebraMap_comp]⟩

/-- **The divided power envelope is functorial in the ring--ideal pair and in the divided power
base.**  A ring map `g : B → B'` carrying `J` into `J'` and compatible with a divided power
morphism `a : A → A'` of the bases induces a divided power morphism of the envelopes over `a`.

This is the universal property [Stacks, Tag 07H8] of the envelope of `J`, applied with the
envelope of `J'` as the target divided power ring: that property quantifies over *every* divided
power ring over `A`, so the target may perfectly well be an envelope for another ideal in another
ring over another base. -/
noncomputable def envelopePairMap (D : DividedPowerEnvelope A f J hJ)
    (D' : DividedPowerEnvelope A' f' J' hJ')
    (a : DividedPowers.DPMorphism A.dividedPowers A'.dividedPowers)
    (g : B →+* B') (hgJ : J.map g ≤ J') (hga : g.comp f = f'.comp a.toRingHom) :
    {q : DividedPowers.DPMorphism D.object.dividedPowers D'.object.dividedPowers //
      q.comp D.structureMap = D'.structureMap.comp a} :=
  (D.homEquiv D'.object (D'.structureMap.comp a)).symm
    (envelopePairHomOver D' a g hgJ hga)

/-- **The induced morphism of envelopes agrees with `g` on the image of `B`.**  Together with
`Crystalline.envelopeHom_ext` this determines it. -/
lemma envelopePairMap_algebraMap (D : DividedPowerEnvelope A f J hJ)
    (D' : DividedPowerEnvelope A' f' J' hJ')
    (a : DividedPowers.DPMorphism A.dividedPowers A'.dividedPowers)
    (g : B →+* B') (hgJ : J.map g ≤ J') (hga : g.comp f = f'.comp a.toRingHom) (x : B) :
    (envelopePairMap D D' a g hgJ hga).1.toRingHom (D.algebraMap.toRingHom x) =
      D'.algebraMap.toRingHom (g x) := by
  have hcomp : IdealPair.Hom.comp
      (IdealPair.Hom.ofDPMorphism (envelopePairMap D D' a g hgJ hga).1) D.algebraMap =
      IdealPair.Hom.comp D'.algebraMap (IdealPair.Hom.ofRingHom g hgJ) :=
    (D.homEquiv_apply D'.object (D'.structureMap.comp a)
      (envelopePairMap D D' a g hgJ hga)).symm.trans
      (congrArg Subtype.val ((D.homEquiv D'.object (D'.structureMap.comp a)).apply_symm_apply
        (envelopePairHomOver D' a g hgJ hga)))
  exact congrArg (fun z : IdealPair.Hom J D'.object.ideal => z.toRingHom x) hcomp

/-- The induced morphism of envelopes is compatible with the base, read on elements. -/
lemma envelopePairMap_structureMap (D : DividedPowerEnvelope A f J hJ)
    (D' : DividedPowerEnvelope A' f' J' hJ')
    (a : DividedPowers.DPMorphism A.dividedPowers A'.dividedPowers)
    (g : B →+* B') (hgJ : J.map g ≤ J') (hga : g.comp f = f'.comp a.toRingHom) (z : A) :
    (envelopePairMap D D' a g hgJ hga).1.toRingHom (D.structureMap.toRingHom z) =
      D'.structureMap.toRingHom (a.toRingHom z) :=
  DFunLike.congr_fun (congrArg DividedPowers.DPMorphism.toRingHom
    (envelopePairMap D D' a g hgJ hga).2) z

/-- **The induced morphism of envelopes is the only one with its two restrictions.**  This is
`Crystalline.envelopeHom_ext` in the form every use below takes: a divided power morphism of
envelopes which lies over `a` and agrees with `g` on the image of `B` *is*
`Crystalline.envelopePairMap`. -/
lemma eq_envelopePairMap (D : DividedPowerEnvelope A f J hJ)
    (D' : DividedPowerEnvelope A' f' J' hJ')
    (a : DividedPowers.DPMorphism A.dividedPowers A'.dividedPowers)
    (g : B →+* B') (hgJ : J.map g ≤ J') (hga : g.comp f = f'.comp a.toRingHom)
    (θ : DividedPowers.DPMorphism D.object.dividedPowers D'.object.dividedPowers)
    (hθa : θ.comp D.structureMap = D'.structureMap.comp a)
    (hθ : ∀ x : B, θ.toRingHom (D.algebraMap.toRingHom x) = D'.algebraMap.toRingHom (g x)) :
    θ = (envelopePairMap D D' a g hgJ hga).1 := by
  refine envelopeHom_ext D D'.object _ _ ?_ ?_
  · rw [hθa, (envelopePairMap D D' a g hgJ hga).2]
  · exact RingHom.ext fun x => (hθ x).trans (envelopePairMap_algebraMap D D' a g hgJ hga x).symm

/-- **The morphism of envelopes induced by the identity is the identity.** -/
lemma envelopePairMap_id (D : DividedPowerEnvelope A f J hJ)
    (hgJ : J.map (RingHom.id B) ≤ J)
    (hga : (RingHom.id B).comp f =
      f.comp (DividedPowers.DPMorphism.id A.dividedPowers).toRingHom) :
    (envelopePairMap D D (DividedPowers.DPMorphism.id A.dividedPowers) (RingHom.id B)
        hgJ hga).1 = DividedPowers.DPMorphism.id D.object.dividedPowers :=
  (eq_envelopePairMap D D (DividedPowers.DPMorphism.id A.dividedPowers) (RingHom.id B) hgJ hga
    (DividedPowers.DPMorphism.id D.object.dividedPowers)
    (dpMorphism_comp_id _) fun _ => rfl).symm

/-- **The morphisms of envelopes compose.**  Both sides are compatible with the base and restrict
to `g' ∘ g` on the image of `B`, so they agree by the uniqueness half of the universal
property. -/
lemma envelopePairMap_comp (D : DividedPowerEnvelope A f J hJ)
    (D' : DividedPowerEnvelope A' f' J' hJ') (D'' : DividedPowerEnvelope A'' f'' J'' hJ'')
    (a : DividedPowers.DPMorphism A.dividedPowers A'.dividedPowers)
    (a' : DividedPowers.DPMorphism A'.dividedPowers A''.dividedPowers)
    (g : B →+* B') (hgJ : J.map g ≤ J') (hga : g.comp f = f'.comp a.toRingHom)
    (g' : B' →+* B'') (hgJ' : J'.map g' ≤ J'') (hga' : g'.comp f' = f''.comp a'.toRingHom)
    (hgJc : J.map (g'.comp g) ≤ J'')
    (hgac : (g'.comp g).comp f = f''.comp (a'.comp a).toRingHom) :
    (envelopePairMap D D'' (a'.comp a) (g'.comp g) hgJc hgac).1 =
      (envelopePairMap D' D'' a' g' hgJ' hga').1.comp
        (envelopePairMap D D' a g hgJ hga).1 := by
  refine envelopeHom_ext D D''.object _ _ ?_ ?_
  · apply DividedPowers.DPMorphism.ext
    funext z
    show (envelopePairMap D D'' (a'.comp a) (g'.comp g) hgJc hgac).1.toRingHom
        (D.structureMap.toRingHom z) =
      (envelopePairMap D' D'' a' g' hgJ' hga').1.toRingHom
        ((envelopePairMap D D' a g hgJ hga).1.toRingHom (D.structureMap.toRingHom z))
    rw [envelopePairMap_structureMap D D'' (a'.comp a) (g'.comp g) hgJc hgac z,
      envelopePairMap_structureMap D D' a g hgJ hga z,
      envelopePairMap_structureMap D' D'' a' g' hgJ' hga' (a.toRingHom z)]
    rfl
  · apply RingHom.ext
    intro x
    show (envelopePairMap D D'' (a'.comp a) (g'.comp g) hgJc hgac).1.toRingHom
        (D.algebraMap.toRingHom x) =
      (envelopePairMap D' D'' a' g' hgJ' hga').1.toRingHom
        ((envelopePairMap D D' a g hgJ hga).1.toRingHom (D.algebraMap.toRingHom x))
    rw [envelopePairMap_algebraMap D D'' (a'.comp a) (g'.comp g) hgJc hgac x,
      envelopePairMap_algebraMap D D' a g hgJ hga x,
      envelopePairMap_algebraMap D' D'' a' g' hgJ' hga' (g x)]
    rfl

end PairMap

/-! ### Envelopes over a fixed divided power base -/

section IdealMap

variable {A : DividedPowerRing.{u}} {B₀ B₁ B₂ : Type v}
  [CommRing B₀] [CommRing B₁] [CommRing B₂]
  {f₀ : A →+* B₀} {J₀ : Ideal B₀} {hJ₀ : A.ideal.map f₀ ≤ J₀}
  {f₁ : A →+* B₁} {J₁ : Ideal B₁} {hJ₁ : A.ideal.map f₁ ≤ J₁}
  {f₂ : A →+* B₂} {J₂ : Ideal B₂} {hJ₂ : A.ideal.map f₂ ≤ J₂}

/-- **The transition morphism of envelopes over a fixed divided power base.**  This is
`Crystalline.envelopePairMap` along the identity of `A`, which is the shape the Čech transitions
`D_{α ∘ φ} → D_α` of [Stacks, Tag 07MM] take: there the base `A = Γ(S, ⊤)` is the same for every
tuple and only the target `C_α` moves. -/
noncomputable def envelopeIdealMap (D₀ : DividedPowerEnvelope A f₀ J₀ hJ₀)
    (D₁ : DividedPowerEnvelope A f₁ J₁ hJ₁) (g : B₀ →+* B₁) (hgJ : J₀.map g ≤ J₁)
    (hgf : g.comp f₀ = f₁) :
    {q : DividedPowers.DPMorphism D₀.object.dividedPowers D₁.object.dividedPowers //
      q.comp D₀.structureMap = D₁.structureMap} :=
  ⟨(envelopePairMap D₀ D₁ (DividedPowers.DPMorphism.id A.dividedPowers) g hgJ hgf).1, by
    rw [(envelopePairMap D₀ D₁ (DividedPowers.DPMorphism.id A.dividedPowers) g hgJ hgf).2]
    apply DividedPowers.DPMorphism.ext
    funext z
    rfl⟩

/-- The transition morphism over a fixed base agrees with `g` on the image of `B₀`. -/
lemma envelopeIdealMap_algebraMap (D₀ : DividedPowerEnvelope A f₀ J₀ hJ₀)
    (D₁ : DividedPowerEnvelope A f₁ J₁ hJ₁) (g : B₀ →+* B₁) (hgJ : J₀.map g ≤ J₁)
    (hgf : g.comp f₀ = f₁) (x : B₀) :
    (envelopeIdealMap D₀ D₁ g hgJ hgf).1.toRingHom (D₀.algebraMap.toRingHom x) =
      D₁.algebraMap.toRingHom (g x) :=
  envelopePairMap_algebraMap D₀ D₁ (DividedPowers.DPMorphism.id A.dividedPowers) g hgJ hgf x

/-- The transition morphism over a fixed base is compatible with the base, read on elements. -/
lemma envelopeIdealMap_structureMap (D₀ : DividedPowerEnvelope A f₀ J₀ hJ₀)
    (D₁ : DividedPowerEnvelope A f₁ J₁ hJ₁) (g : B₀ →+* B₁) (hgJ : J₀.map g ≤ J₁)
    (hgf : g.comp f₀ = f₁) (z : A) :
    (envelopeIdealMap D₀ D₁ g hgJ hgf).1.toRingHom (D₀.structureMap.toRingHom z) =
      D₁.structureMap.toRingHom z :=
  DFunLike.congr_fun (congrArg DividedPowers.DPMorphism.toRingHom
    (envelopeIdealMap D₀ D₁ g hgJ hgf).2) z

/-- **The transition morphism over a fixed base is the only one with its two restrictions.**
This is what makes the transitions `D_{α ∘ φ} → D_α` of [Stacks, Tag 07MM] *strictly* functorial:
`CechPresentation.tupleRename` is strictly functorial, so the two candidate composites agree on
the image of the polynomial algebra, and this lemma then identifies them. -/
lemma eq_envelopeIdealMap (D₀ : DividedPowerEnvelope A f₀ J₀ hJ₀)
    (D₁ : DividedPowerEnvelope A f₁ J₁ hJ₁) (g : B₀ →+* B₁) (hgJ : J₀.map g ≤ J₁)
    (hgf : g.comp f₀ = f₁)
    (θ : DividedPowers.DPMorphism D₀.object.dividedPowers D₁.object.dividedPowers)
    (hθa : θ.comp D₀.structureMap = D₁.structureMap)
    (hθ : ∀ x : B₀, θ.toRingHom (D₀.algebraMap.toRingHom x) = D₁.algebraMap.toRingHom (g x)) :
    θ = (envelopeIdealMap D₀ D₁ g hgJ hgf).1 :=
  eq_envelopePairMap D₀ D₁ (DividedPowers.DPMorphism.id A.dividedPowers) g hgJ hgf θ
    (by rw [hθa, dpMorphism_comp_id]) hθ

end IdealMap

/-! ### Polynomial presentations across a morphism of situations -/

section Polynomial

variable {s t : AffineCrystallineSituation.{u, v}}

/-- **Functoriality of the divided power envelope of a polynomial presentation across a morphism
of affine crystalline situations.**  This is `Crystalline.polynomialEnvelopeMap` with the
restriction to one situation removed: the two presentations may present the targets of two
different situations, provided a morphism of situations relates them and the renaming of the
variables is compatible with it.

The hypothesis `hrC` says that `r` is a map over the base morphism, and `hr` that the square of
presentations commutes.  For `s = t` and the identity morphism they say exactly that `r` is a map
of `s.A`-algebras commuting with the two presentations, which is
`Crystalline.polynomialEnvelopeMapOver_eq_polynomialEnvelopeMap`. -/
noncomputable def polynomialEnvelopeMapOver (σ : AffineCrystallineSituation.Hom s t)
    {ι κ : Type w} (f : MvPolynomial ι s.A →ₐ[s.A] s.C) (g : MvPolynomial κ t.A →ₐ[t.A] t.C)
    (r : MvPolynomial ι s.A →+* MvPolynomial κ t.A)
    (hrC : ∀ b : s.A, r (MvPolynomial.C b) = MvPolynomial.C (σ.base.toRingHom b))
    (hr : g.toRingHom.comp r = σ.target.comp f.toRingHom) :
    {q : DividedPowers.DPMorphism (polynomialDividedPowerEnvelope s f).object.dividedPowers
        (polynomialDividedPowerEnvelope t g).object.dividedPowers //
      q.comp (polynomialDividedPowerEnvelope s f).structureMap =
        (polynomialDividedPowerEnvelope t g).structureMap.comp σ.base} :=
  envelopePairMap (polynomialDividedPowerEnvelope s f) (polynomialDividedPowerEnvelope t g)
    σ.base r
    (by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have hx' : g (r x) = σ.target (f x) := RingHom.congr_fun hr x
      change g (r x) = 0
      rw [hx', show f x = 0 from hx, map_zero])
    (RingHom.ext hrC)

/-- The induced morphism agrees with the renaming of the variables on the image of the polynomial
algebra. -/
lemma polynomialEnvelopeMapOver_polynomial (σ : AffineCrystallineSituation.Hom s t)
    {ι κ : Type w} (f : MvPolynomial ι s.A →ₐ[s.A] s.C) (g : MvPolynomial κ t.A →ₐ[t.A] t.C)
    (r : MvPolynomial ι s.A →+* MvPolynomial κ t.A)
    (hrC : ∀ b : s.A, r (MvPolynomial.C b) = MvPolynomial.C (σ.base.toRingHom b))
    (hr : g.toRingHom.comp r = σ.target.comp f.toRingHom) (x : MvPolynomial ι s.A) :
    (polynomialEnvelopeMapOver σ f g r hrC hr).1
        ((polynomialDividedPowerEnvelope s f).algebraMap.toRingHom x) =
      (polynomialDividedPowerEnvelope t g).algebraMap.toRingHom (r x) :=
  envelopePairMap_algebraMap (polynomialDividedPowerEnvelope s f)
    (polynomialDividedPowerEnvelope t g) σ.base r _ _ x

/-- **Over the identity morphism of one situation the construction is
`Crystalline.polynomialEnvelopeMap`.**  So `Crystalline.polynomialEnvelopeMapOver` is a genuine
generalization of that construction and not a second, parallel one. -/
lemma polynomialEnvelopeMapOver_eq_polynomialEnvelopeMap (s : AffineCrystallineSituation.{u, v})
    {ι κ : Type w} (f : MvPolynomial ι s.A →ₐ[s.A] s.C) (g : MvPolynomial κ s.A →ₐ[s.A] s.C)
    (r : MvPolynomial ι s.A →ₐ[s.A] MvPolynomial κ s.A) (hr : g.comp r = f)
    (hrC : ∀ b : s.A, r.toRingHom (MvPolynomial.C b) =
      MvPolynomial.C ((AffineCrystallineSituation.Hom.id s).base.toRingHom b))
    (hr' : g.toRingHom.comp r.toRingHom =
      (AffineCrystallineSituation.Hom.id s).target.comp f.toRingHom) :
    (polynomialEnvelopeMapOver (AffineCrystallineSituation.Hom.id s) f g r.toRingHom hrC hr').1 =
      (polynomialEnvelopeMap s f g r hr).1 := by
  refine envelopeHom_ext (polynomialDividedPowerEnvelope s f)
    (polynomialDividedPowerEnvelope s g).object _ _ ?_ ?_
  · rw [(polynomialEnvelopeMapOver (AffineCrystallineSituation.Hom.id s) f g r.toRingHom hrC
      hr').2, (polynomialEnvelopeMap s f g r hr).2]
    exact dpMorphism_comp_id _
  · apply RingHom.ext
    intro x
    show (polynomialEnvelopeMapOver (AffineCrystallineSituation.Hom.id s) f g r.toRingHom hrC
          hr').1 ((polynomialDividedPowerEnvelope s f).algebraMap.toRingHom x) =
      (polynomialEnvelopeMap s f g r hr).1
        ((polynomialDividedPowerEnvelope s f).algebraMap.toRingHom x)
    rw [polynomialEnvelopeMapOver_polynomial, polynomialEnvelopeMap_polynomial]
    rfl

end Polynomial

/-! ### Completion of the induced morphisms -/

section Completion

variable {R T U : Type*} [CommRing R] [CommRing T] [CommRing U]

/-- **The `p`-adic completion of the identity is the identity.**  Together with
`Crystalline.adicCompletionRingMap_comp` this makes `Crystalline.adicCompletionRingMap` a functor,
which is what carries the strict functoriality of a family of morphisms of envelopes over to
their completions. -/
lemma adicCompletionRingMap_id (p : ℕ) :
    adicCompletionRingMap (RingHom.id R) (map_pAdicIdeal_le p (RingHom.id R)) =
      RingHom.id (AdicCompletion (DividedPowers.pAdicIdeal (A := R) p) R) := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext
  intro n
  obtain ⟨a, ha⟩ := Submodule.mkQ_surjective
    (DividedPowers.pAdicIdeal (A := R) p ^ n • (⊤ : Submodule R R)) (x.val n)
  show adicQuotientMap (ringHomₛₗ (RingHom.id R)) (map_pAdicIdeal_le p (RingHom.id R)) n
    (x.val n) = x.val n
  rw [← ha]
  rfl

/-- **The `p`-adic completions of two composable ring maps compose.** -/
lemma adicCompletionRingMap_comp (p : ℕ) (σ : R →+* T) (τ : T →+* U) :
    adicCompletionRingMap (τ.comp σ) (map_pAdicIdeal_le p (τ.comp σ)) =
      (adicCompletionRingMap τ (map_pAdicIdeal_le p τ)).comp
        (adicCompletionRingMap σ (map_pAdicIdeal_le p σ)) := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext
  intro n
  obtain ⟨a, ha⟩ := Submodule.mkQ_surjective
    (DividedPowers.pAdicIdeal (A := R) p ^ n • (⊤ : Submodule R R)) (x.val n)
  show adicQuotientMap (ringHomₛₗ (τ.comp σ)) (map_pAdicIdeal_le p (τ.comp σ)) n (x.val n) =
    adicQuotientMap (ringHomₛₗ τ) (map_pAdicIdeal_le p τ) n
      (adicQuotientMap (ringHomₛₗ σ) (map_pAdicIdeal_le p σ) n (x.val n))
  rw [← ha]
  rfl

end Completion

end Crystalline

end
