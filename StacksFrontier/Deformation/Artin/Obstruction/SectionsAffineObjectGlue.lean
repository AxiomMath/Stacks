module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsBaseChangeTensor

/-!
# The base change of an `AffineObject` morphism, and its identity and composition laws

The obstruction theory of Stacks 07YH is indexed by `Deformation.Artin.AffineObject`: an object
`x` of the fibred category over the spectrum of a site algebra `A`. Its geometric input, on the
other hand — the base-change immersion `W_{A₁} → W_A` that the map of obstruction modules of
clause (2) is built from — is `Deformation.Artin.SectionsSheaf.baseChangeMap q (quotHom ψ t)`,
which is indexed by a ring map `ψ : A → A₁` and a morphism `t : Spec A → S`.

This file is the dictionary between the two, and it is what the coherence conditions of clause
(2) — `map_id`, `map_comp` and `map_local` of `Deformation.Artin.ObstructionTheory` — wait on at
the `AffineObject` level.

## Main results

* `Deformation.Artin.SiteAlgebra.Hom.specMap_comp_toScheme` — **the identification**: a map of
  site algebras `a → b` has `Spec b → Spec a → S` equal to the structure morphism of `b`, so the
  base of `b` *is* the base change of the base of `a` along the ring map. The two are **equal**,
  not merely isomorphic.
* `Deformation.Artin.SectionsSheaf.quotOver_affineHom_eq` — consequently
  `quotOver (ψ) (base of P) = Over.mk (base of Q)` for a morphism `P ⟶ Q` of affine objects.
* `Deformation.Artin.SectionsSheaf.baseChangeMap_quotHom_id` and
  `..baseChangeMap_quotHom_comp` — **the identity and composition laws for the base-change
  immersion**: along a ring map whose spectrum is the identity the immersion is the identity
  (transported along the equality of bases), and along a composite it is the composite.
* `Deformation.Artin.SectionsSheaf.baseChangeMap_quotHom_affineHom_id` and
  `..baseChangeMap_quotHom_affineHom_comp` — the same two laws at
  `Deformation.Artin.AffineObject.Hom.id` and `..Hom.comp`.

## Implementation notes

**The mismatch is an equality of objects, not an isomorphism of two pullbacks.** `quotOver ψ t`
is `Over.mk (Spec ψ ≫ t)` and the base of the target object is `Over.mk t₁`; the two differ only
through the function `Over.mk` applied to the two morphisms `Spec ψ ≫ t` and `t₁`, which are
equal. So `congrArg` settles the object comparison, and the base changes differ by the `eqToHom`
of that equality — no canonical comparison of two fibre products is needed, and none is
constructed here.

Every statement that would mention `Spec.map` of a composite or of an identity ring map inside a
dependent type carries the composite or the identity as an *equality hypothesis* on a variable
instead, and discharges it by `subst`; the laws are then applied at an `AffineObject` morphism
with the equality supplied by `CommRingCat.ofHom_comp` resp. `CommRingCat.ofHom_id`. This is not
a stylistic choice. Proving the composition law for `quotHom` directly — by `Over.OverMorphism.ext`
followed by `Spec.map_comp` on the `left` components — elaborates but then **exhausts the kernel's
deterministic timeout**, because the kernel is left comparing `Over` records whose components are
`Spec` of a `CommRingCat`. Factoring the content through `overMk`, where the schemes and their
morphisms are opaque variables, costs a fraction of a second.

The pullback-object equalities and the `Over`-object equalities are taken as hypotheses in the
laws rather than built into their statements. Proofs of an equality are definitionally equal, so a
consumer may discharge them with whichever proof term it has; `quotOver_id_eq`,
`quotOver_comp_eq` and `baseChangeObj_congr` produce them.

No `@[stacks 07YH]` attribute: these are the identity and composition laws of the *geometric*
base change, the dictionary between two indexings used inside this development, not a clause of
that tag. The clauses they serve are the `map_id`, `map_comp` and `map_local` fields of
`Deformation.Artin.ObstructionTheory`, which are not proved for this example.

## References

* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
* [Stacks Project, Tag 07YG](https://stacks.math.columbia.edu/tag/07YG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v w

namespace Deformation.Artin

/-! ### The base of the target of a morphism of site algebras -/

section Site

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The base of the target is the base change of the base of the source.** For a map
`a → b` of site algebras over `S`, the composite `Spec b → Spec a → S` of the spectrum of the
ring map with the structure morphism of `a` *is* the structure morphism of `b`.

This is the identification the `AffineObject` indexing of an obstruction theory and the
`(ψ, t)` indexing of the base-change immersion of Stacks 07YH differ by. The two morphisms are
equal, so the two fibre products `W_b` and `W_{Spec ψ ≫ t}` are equal objects and no comparison
isomorphism is involved. -/
theorem SiteAlgebra.Hom.specMap_comp_toScheme {a b : SiteAlgebra B S hS}
    (f : SiteAlgebra.Hom a b) :
    Spec.map (CommRingCat.ofHom f.ringMap) ≫ a.toScheme = b.toScheme := by
  rw [← f.specMap_spec, ← CategoryTheory.Functor.map_comp]
  exact congrArg B.inclusion.map (Over.w f.specMap)

variable {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS}

/-- The ring map of an identity morphism of affine objects is the identity of `CommRingCat`. -/
theorem AffineObject.Hom.ofHom_ringMap_id (P : AffineObject B S hS p) :
    CommRingCat.ofHom (AffineObject.Hom.id P).alg.ringMap =
      𝟙 (CommRingCat.of P.alg.carrier) :=
  CommRingCat.ofHom_id

/-- The spectrum of the ring map of an identity morphism of affine objects is the identity. -/
theorem AffineObject.Hom.specMap_ofHom_ringMap_id (P : AffineObject B S hS p) :
    Spec.map (CommRingCat.ofHom (AffineObject.Hom.id P).alg.ringMap) =
      𝟙 (Spec (CommRingCat.of P.alg.carrier)) := by
  rw [AffineObject.Hom.ofHom_ringMap_id, Spec.map_id]

/-- The ring map of a composite of morphisms of affine objects is the composite of the ring
maps. -/
theorem AffineObject.Hom.ofHom_ringMap_comp {P Q R : AffineObject B S hS p}
    (h : AffineObject.Hom P Q) (k : AffineObject.Hom Q R) :
    CommRingCat.ofHom (h.comp k).alg.ringMap =
      CommRingCat.ofHom h.alg.ringMap ≫ CommRingCat.ofHom k.alg.ringMap :=
  CommRingCat.ofHom_comp _ _

end Site

end Deformation.Artin

namespace Deformation.Artin.SectionsSheaf

/-! ### Morphisms of schemes over `S` of the form `Over.mk (g ≫ t) ⟶ Over.mk t` -/

section Generic

variable {S : Scheme.{u}}

/-- The morphism `Over.mk (g ≫ t) ⟶ Over.mk t` of schemes over `S` induced by `g`. This is
`quotHom` with the morphism of spectra abstracted to a morphism of schemes; the identity and
composition laws are proved at this generality because here the schemes and their morphisms are
opaque, and the kernel never unfolds a `Spec`. -/
abbrev overMk {X Y : Scheme.{u}} (g : X ⟶ Y) (t : Y ⟶ S) : Over.mk (g ≫ t) ⟶ Over.mk t :=
  Over.homMk g rfl

/-- Replacing `g` by an equal morphism changes `overMk g t` by the transport of the equality of
the two objects over `S`. -/
theorem overMk_congr {X Y : Scheme.{u}} {g g' : X ⟶ Y} (hg : g = g') (t : Y ⟶ S)
    (h : Over.mk (g ≫ t) = Over.mk (g' ≫ t)) :
    overMk g t = eqToHom h ≫ overMk g' t := by
  subst hg
  simp

/-- **The identity law**: `overMk` of an identity is the transport along `𝟙 ≫ t = t`. -/
theorem overMk_id {X : Scheme.{u}} (t : X ⟶ S) (h : Over.mk (𝟙 X ≫ t) = Over.mk t) :
    overMk (𝟙 X) t = eqToHom h := by
  refine Over.OverMorphism.ext ?_
  simp

/-- **The composition law**: `overMk` of a composite is the composite of the two `overMk`s,
transported along the associativity of the three morphisms. -/
theorem overMk_comp {X Y Z : Scheme.{u}} (g₂ : Z ⟶ Y) (g₁ : Y ⟶ X) (t : X ⟶ S)
    (h : Over.mk ((g₂ ≫ g₁) ≫ t) = Over.mk (g₂ ≫ g₁ ≫ t)) :
    overMk (g₂ ≫ g₁) t = eqToHom h ≫ overMk g₂ (g₁ ≫ t) ≫ overMk g₁ t := by
  refine Over.OverMorphism.ext ?_
  simp

end Generic

/-! ### The base-change immersion is functorial in the morphism of schemes over `S` -/

section BaseChange

variable {S W : Scheme.{u}} (q : W ⟶ S)

/-- The equality of fibre products induced by an equality of objects over `S`. -/
theorem baseChangeObj_congr {T T' : Over S} (e : T = T') :
    pullback T.hom q = pullback T'.hom q :=
  congrArg (fun U : Over S => pullback U.hom q) e

/-- **The base-change immersion is multiplicative**: it is the `left` component of the image of
a functor. -/
theorem baseChangeMap_comp' {T T' T'' : Over S} (α : T'' ⟶ T') (β : T' ⟶ T) :
    baseChangeMap q (α ≫ β) = baseChangeMap q α ≫ baseChangeMap q β := by
  rw [baseChangeMap, CategoryTheory.Functor.map_comp, Over.comp_left]

/-- **The base change of a transport is a transport.** -/
theorem baseChangeMap_eqToHom {T T' : Over S} (h : T = T')
    (h' : pullback T.hom q = pullback T'.hom q) :
    baseChangeMap q (eqToHom h) = eqToHom h' := by
  subst h
  simp [baseChangeMap]

end BaseChange

/-! ### The identity and composition laws for `quotHom` and its base change -/

section Quot

variable {S W : Scheme.{u}} (q : W ⟶ S) {A A₁ A₂ : CommRingCat.{u}}

/-- `quotHom` is `overMk` at the spectrum of the ring map. -/
theorem quotHom_eq_overMk (ψ : A ⟶ A₁) (t : Spec A ⟶ S) :
    quotHom ψ t = overMk (Spec.map ψ) t :=
  rfl

/-- The base of the target of `quotHom ψ t` is `Over.mk t₁` whenever `Spec ψ ≫ t` is `t₁`. This
is `congrArg` of `Over.mk`: no comparison of fibre products is involved. -/
theorem quotOver_eq (ψ : A ⟶ A₁) {t : Spec A ⟶ S} {t₁ : Spec A₁ ⟶ S}
    (e : Spec.map ψ ≫ t = t₁) : quotOver ψ t = Over.mk t₁ :=
  congrArg (fun u => Over.mk u) e

/-- Along a ring map whose spectrum is the identity the base is unchanged. -/
theorem quotOver_id_eq (ψ : A ⟶ A) (hψ : Spec.map ψ = 𝟙 (Spec A)) (t : Spec A ⟶ S) :
    quotOver ψ t = Over.mk t :=
  quotOver_eq ψ (by rw [hψ, Category.id_comp])

/-- Along a composite ring map the base is the base change of the base change. -/
theorem quotOver_comp_eq (ψ : A ⟶ A₂) (ψ₁ : A ⟶ A₁) (ψ₂ : A₁ ⟶ A₂) (hψ : ψ = ψ₁ ≫ ψ₂)
    (t : Spec A ⟶ S) : quotOver ψ t = quotOver ψ₂ (Spec.map ψ₁ ≫ t) := by
  subst hψ
  exact quotOver_eq _ (by rw [Spec.map_comp, Category.assoc])

/-- **The identity law for `quotHom`**: along a ring map whose spectrum is the identity,
`quotHom` is the transport along the equality of bases. -/
theorem quotHom_eq_eqToHom (ψ : A ⟶ A) (hψ : Spec.map ψ = 𝟙 (Spec A)) (t : Spec A ⟶ S)
    (h : quotOver ψ t = Over.mk t) : quotHom ψ t = eqToHom h := by
  rw [quotHom_eq_overMk, overMk_congr hψ t (by rw [hψ]), overMk_id t (by rw [Category.id_comp]),
    eqToHom_trans]

/-- **The composition law for `quotHom`**: along a composite ring map it is the composite of the
two, transported along the equality of bases. -/
theorem quotHom_comp_eq (ψ₁ : A ⟶ A₁) (ψ₂ : A₁ ⟶ A₂) (t : Spec A ⟶ S)
    (h : quotOver (ψ₁ ≫ ψ₂) t = quotOver ψ₂ (Spec.map ψ₁ ≫ t)) :
    quotHom (ψ₁ ≫ ψ₂) t = eqToHom h ≫ quotHom ψ₂ (Spec.map ψ₁ ≫ t) ≫ quotHom ψ₁ t := by
  rw [quotHom_eq_overMk, overMk_congr (Spec.map_comp ψ₁ ψ₂) t (by rw [Spec.map_comp]),
    overMk_comp (Spec.map ψ₂) (Spec.map ψ₁) t (by rw [Category.assoc]), ← Category.assoc,
    eqToHom_trans]

/-- **The identity law for the base-change immersion.** Along a ring map whose spectrum is the
identity morphism of `Spec A`, the base-change immersion `W_{A} → W_{A}` is the identity, read
through the equality of the two bases. This is the `AffineObject`-level fact that `map_id` and
`map_local` of clause (2) of Stacks 07YG rest on for the example of Stacks 07YH. -/
theorem baseChangeMap_quotHom_id (ψ : A ⟶ A) (hψ : Spec.map ψ = 𝟙 (Spec A)) (t : Spec A ⟶ S)
    (h : quotOver ψ t = Over.mk t)
    (h' : pullback (quotOver ψ t).hom q = pullback (Over.mk t).hom q) :
    baseChangeMap q (quotHom ψ t) = eqToHom h' := by
  rw [quotHom_eq_eqToHom ψ hψ t h, baseChangeMap_eqToHom q h h']

/-- **The composition law for the base-change immersion.** Along a composite of ring maps the
base-change immersion is the composite of the two base-change immersions, read through the
equality of the two bases. This is the `AffineObject`-level fact that `map_comp` of clause (2) of
Stacks 07YG rests on for the example of Stacks 07YH. -/
theorem baseChangeMap_quotHom_comp (ψ₁ : A ⟶ A₁) (ψ₂ : A₁ ⟶ A₂) (t : Spec A ⟶ S)
    (h : quotOver (ψ₁ ≫ ψ₂) t = quotOver ψ₂ (Spec.map ψ₁ ≫ t))
    (h' : pullback (quotOver (ψ₁ ≫ ψ₂) t).hom q =
      pullback (quotOver ψ₂ (Spec.map ψ₁ ≫ t)).hom q) :
    baseChangeMap q (quotHom (ψ₁ ≫ ψ₂) t) =
      eqToHom h' ≫ baseChangeMap q (quotHom ψ₂ (Spec.map ψ₁ ≫ t)) ≫
        baseChangeMap q (quotHom ψ₁ t) := by
  rw [quotHom_comp_eq ψ₁ ψ₂ t h, baseChangeMap_comp', baseChangeMap_comp',
    baseChangeMap_eqToHom q h h']

/-- The composition law for the base-change immersion, with the composite ring map carried as a
variable with an equality hypothesis so that it may be instantiated at an `AffineObject`
morphism without rewriting inside a dependent type. -/
theorem baseChangeMap_quotHom_of_eq_comp (ψ : A ⟶ A₂) (ψ₁ : A ⟶ A₁) (ψ₂ : A₁ ⟶ A₂)
    (hψ : ψ = ψ₁ ≫ ψ₂) (t : Spec A ⟶ S)
    (h : quotOver ψ t = quotOver ψ₂ (Spec.map ψ₁ ≫ t))
    (h' : pullback (quotOver ψ t).hom q = pullback (quotOver ψ₂ (Spec.map ψ₁ ≫ t)).hom q) :
    baseChangeMap q (quotHom ψ t) =
      eqToHom h' ≫ baseChangeMap q (quotHom ψ₂ (Spec.map ψ₁ ≫ t)) ≫
        baseChangeMap q (quotHom ψ₁ t) := by
  subst hψ
  exact baseChangeMap_quotHom_comp q ψ₁ ψ₂ t h h'

end Quot

/-! ### The two laws at a morphism of affine objects -/

section AffineObjectGlue

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : Type v}
  [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {W : Scheme.{u}} (q : W ⟶ S)

/-- **The base of the target of a morphism of affine objects is the base change of the base of
its source.** This is `SiteAlgebra.Hom.specMap_comp_toScheme` read in the spelling of the
base-change data of Stacks 07YH. -/
theorem quotOver_affineHom_eq {P Q : AffineObject B S hS p} (h : AffineObject.Hom P Q) :
    quotOver (CommRingCat.ofHom h.alg.ringMap) P.alg.toScheme = Over.mk Q.alg.toScheme :=
  quotOver_eq _ h.alg.specMap_comp_toScheme

/-- **The identity law at `AffineObject.Hom.id`**: the base-change immersion attached to the
identity morphism of an affine object is the identity of `W_A`, read through the equality of the
two bases. -/
theorem baseChangeMap_quotHom_affineHom_id (P : AffineObject B S hS p)
    (h' : pullback (quotOver (CommRingCat.ofHom (AffineObject.Hom.id P).alg.ringMap)
        P.alg.toScheme).hom q = pullback (Over.mk P.alg.toScheme).hom q) :
    baseChangeMap q (quotHom (CommRingCat.ofHom (AffineObject.Hom.id P).alg.ringMap)
      P.alg.toScheme) = eqToHom h' :=
  baseChangeMap_quotHom_id q _ (AffineObject.Hom.specMap_ofHom_ringMap_id P) _
    (quotOver_affineHom_eq (AffineObject.Hom.id P)) h'

/-- The base of a composite of morphisms of affine objects, as an iterated base change. -/
theorem quotOver_affineHom_comp_eq {P Q R : AffineObject B S hS p} (h : AffineObject.Hom P Q)
    (k : AffineObject.Hom Q R) :
    quotOver (CommRingCat.ofHom (h.comp k).alg.ringMap) P.alg.toScheme =
      quotOver (CommRingCat.ofHom k.alg.ringMap)
        (Spec.map (CommRingCat.ofHom h.alg.ringMap) ≫ P.alg.toScheme) :=
  quotOver_comp_eq _ _ _ (AffineObject.Hom.ofHom_ringMap_comp h k) _

/-- **The composition law at `AffineObject.Hom.comp`**: the base-change immersion attached to a
composite of morphisms of affine objects is the composite of the two base-change immersions,
read through the equality of the two bases. -/
theorem baseChangeMap_quotHom_affineHom_comp {P Q R : AffineObject B S hS p}
    (h : AffineObject.Hom P Q) (k : AffineObject.Hom Q R)
    (h' : pullback (quotOver (CommRingCat.ofHom (h.comp k).alg.ringMap)
          P.alg.toScheme).hom q =
      pullback (quotOver (CommRingCat.ofHom k.alg.ringMap)
        (Spec.map (CommRingCat.ofHom h.alg.ringMap) ≫ P.alg.toScheme)).hom q) :
    baseChangeMap q (quotHom (CommRingCat.ofHom (h.comp k).alg.ringMap) P.alg.toScheme) =
      eqToHom h' ≫
        baseChangeMap q (quotHom (CommRingCat.ofHom k.alg.ringMap)
          (Spec.map (CommRingCat.ofHom h.alg.ringMap) ≫ P.alg.toScheme)) ≫
        baseChangeMap q (quotHom (CommRingCat.ofHom h.alg.ringMap) P.alg.toScheme) :=
  baseChangeMap_quotHom_of_eq_comp q _ _ _ (AffineObject.Hom.ofHom_ringMap_comp h k) _
    (quotOver_affineHom_comp_eq h k) h'

end AffineObjectGlue

end Deformation.Artin.SectionsSheaf

end
