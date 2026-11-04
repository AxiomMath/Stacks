module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.IntegralSurjectiveCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CompositeMorphismUnderivedBaseChange

/-!
# Cancelling a surjection from a composite in the étale base change comparison

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of schemes with named composite `gf`, let
`c : Z' ⟶ Z`, and consider commutative squares
```
X' --e--> X      Y' --d--> Y
|f'       |f     |g'       |g
v         v      v         v
Y' --d--> Y      Z' --c--> Z
```
with `q : X' ⟶ Z'` the named composite of `f'` and `g'`.  Stacks 0A4C says that if cohomology
commutes with base change for `f` and for `g ∘ f`, and `f` is surjective, then cohomology
commutes with base change for `g`.  This file proves that statement **in degree zero**: if the
underived comparison `d^{-1} f_* ⟶ f'_* e^{-1}` of the upper square and the underived comparison
`c^{-1} (gf)_* ⟶ q_* e^{-1}` of the rectangle are invertible at every abelian sheaf, and the
unit `A ⟶ f_* f^{-1} A` is a monomorphism for every abelian sheaf `A` on `Y_étale` — which is
what surjectivity of `f` gives — then the underived comparison `c^{-1} g_* ⟶ g'_* d^{-1}` of the
lower square is invertible at every abelian sheaf.

## The argument

Write `τ` for the comparison of the lower square, a natural transformation `g_* ⋙ c^{-1} ⟶
d^{-1} ⋙ g'_*` of **left exact** functors, `g_*` and `g'_*` being right adjoints and `c^{-1}`
and `d^{-1}` being exact.

*The composition formula gives `τ` at a direct image.*  By
`Stacks.EtaleCohomology.etaleAbelianBaseChange_compDirectImage_app` the comparison of the
rectangle at `F` is, up to two isomorphisms, the comparison of the lower square at `f_* F`
followed by `g'_*` of the comparison of the upper square at `F`.  The two hypotheses therefore
leave `τ` invertible at every sheaf of the form `f_* F`.

*Surjectivity makes every sheaf a subsheaf of such a direct image.*  For surjective `f` the unit
`A ⟶ f_* f^{-1} A` is a monomorphism, which is
`Stacks.EtaleCohomology.mono_smallEtaleUnitAb_of_surjective`.  Since `τ` is a transformation of
left exact functors, and left exact functors preserve monomorphisms, invertibility of `τ` at
`f_* f^{-1} A` forces `τ` to be a **monomorphism** at every `A`.

*Left exactness then upgrades the monomorphism to an isomorphism.*  Put `B = f_* f^{-1} A` and
`C = B / A`.  The source `g_* ⋙ c^{-1}` carries the kernel presentation of `A` inside `B` to a
kernel presentation, so a morphism into `(g_* ⋙ c^{-1}) B` killed by the map to
`(g_* ⋙ c^{-1}) C` factors through `(g_* ⋙ c^{-1}) A`.  Applying this to
`(d^{-1} ⋙ g'_*) A ⟶ (d^{-1} ⋙ g'_*) B ≅ (g_* ⋙ c^{-1}) B` — the composite is killed because
`τ` is a monomorphism at `C` — produces a two-sided inverse of `τ` at `A`.

## Main results

* `Stacks.EtaleCohomology.mono_etaleAbelianUnit_of_surjective` — the unit `A ⟶ f_* f^{-1} A` of
  the inverse-image/direct-image adjunction of the proper base change development is a
  monomorphism for a surjective morphism.  This is the only use of surjectivity.
* `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_directImage_of_compDirectImage` — the
  comparison of the lower square is invertible at a direct image along `f`.
* `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_mono_unit` — **Stacks 0A4C in degree
  zero.**

## Implementation notes

**Coefficients and the form of hypothesis (3).**  The proper base change development is written
at coefficients `AddCommGrpCat.{max (u + 1) v}` for an arbitrary `v`, whereas the monomorphy of
the unit along a surjection is available only at `Ab.{u + 1} = AddCommGrpCat.{u + 1}`.  The
cancellation theorem is therefore stated for arbitrary `v` with the monomorphy of the unit as
hypothesis `hunit`, and `Stacks.EtaleCohomology.mono_etaleAbelianUnit_of_surjective` supplies
that hypothesis from `Surjective f` at `v = 0`.  Keeping `v` free is not cosmetic: specialising
the statement of any of the `v`-polymorphic declarations of this development to `v = 0` and
restating it makes the kernel check of the restatement diverge, while at a free `v` the same
statement is checked instantly.

**Two spellings of the same adjunction.**  `Stacks.EtaleCohomology.smallEtaleAdjunctionAb`, in
which the monomorphy of the unit is proved, uses the abstract left adjoint
`CategoryTheory.Functor.sheafPullback` of the direct image, while
`Stacks.EtaleCohomology.etaleAbelianInverseImageDirectImageAdj` uses the left adjoint built as a
left Kan extension followed by sheafification.  The two are different functors with the same
right adjoint, so `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` identifies the two
units up to an isomorphism and monomorphy transfers.

**Opaque witnesses.**  The subobject `A ⟶ f_* f^{-1} A` is passed to the two categorical lemmas
through an existential, so that the comparison between the two spellings
`(f^{-1} ⋙ f_*).obj A` and `f_*(f^{-1} A)` of its target happens once rather than at every
application; done naively the repeated comparison unfolds the sheafification inside the inverse
image and does not terminate.

**What is missing for the full statement.**  Stacks 0A4C is about the derived comparison on
torsion sheaves, and the source's proof reduces it to a degree-zero vanishing statement by
Stacks 0A4B, the equivalence between "cohomology commutes with base change for `f`" and the
vanishing of `R^q f'_* (g')^{-1} I` for injective sheaves of `Z/ℓ`-modules `I`.  That tag is not
formalized in this library — nothing carries it, and neither the relative Leray spectral
sequence for abelian sheaves on a small étale site nor the vanishing it speaks of is available
— so the degree-zero statement is where the argument stops.  The source also assumes `f` and `g`
proper; properness is not used here and is therefore not assumed.

## References

* [Stacks Project, Tag 0A4C](https://stacks.math.columbia.edu/tag/0A4C)
* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
* [Stacks Project, Tag 0A4B](https://stacks.math.columbia.edu/tag/0A4B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

/-! ### Abstract input: a transformation of functors and a subobject

The two lemmas below take every categorical fact they use as an explicit hypothesis rather than
as an instance.  This is deliberate: an instance argument such as `[PreservesFiniteLimits S]` on
a universe-polymorphic lemma makes the kernel check of its instantiation at the sheaf categories
of the small étale sites time out, while the same facts obtained by instance search in the
concrete setting are cheap. -/

section Abstract

variable {C : Type*} [Category* C]

/-- Cancelling three invertible factors from a fourfold composite. -/
private lemma isIso_of_comp_four_eq {V W X Y Z : C} (a : V ⟶ W) (b : W ⟶ X) (c : X ⟶ Y)
    (d : Y ⟶ Z) (m : V ⟶ Z) (hm : m = a ≫ b ≫ c ≫ d) (ha : IsIso a) (hc : IsIso c)
    (hd : IsIso d) (hmi : IsIso m) : IsIso b := by
  have := ha
  have := hc
  have := hd
  have := hmi
  have hb : b = inv a ≫ m ≫ inv d ≫ inv c := by rw [hm]; simp
  rw [hb]
  infer_instance

/-- A morphism with a monomorphic factorisation through it is a monomorphism. -/
private lemma mono_of_comp_eq {X Y Z : C} {a : X ⟶ Y} {b : Y ⟶ Z} {m : X ⟶ Z}
    (h : a ≫ b = m) (hm : Mono m) : Mono a := by
  have := hm
  exact mono_of_mono_fac h

variable {𝒜 : Type*} {ℬ : Type*} [Category* 𝒜] [Category* ℬ]

/-- **A transformation of functors is monomorphic at `A` as soon as it is invertible at an
object `B` containing `A` and the source carries `A ⟶ B` to a monomorphism.**  Naturality turns
the composite of the image of `A ⟶ B` with the invertible component at `B` into the component at
`A` followed by the image of `A ⟶ B` under the target. -/
private lemma mono_app_of_mono_map {S T : 𝒜 ⥤ ℬ} (τ : S ⟶ T) {A B : 𝒜} (u : A ⟶ B)
    (hSu : Mono (S.map u)) (hB : IsIso (τ.app B)) : Mono (τ.app A) := by
  have := hSu
  have := hB
  have hmono : Mono (S.map u ≫ τ.app B) := mono_comp _ _
  rw [τ.naturality u] at hmono
  constructor
  intro W p r hpr
  refine hmono.right_cancellation p r ?_
  rw [← Category.assoc, ← Category.assoc, hpr]

/-- **A transformation invertible at `B` is invertible at `A` once a factorisation of the
target's `A ⟶ B` through the source's is given.**  The morphism `k` is the candidate inverse;
monomorphy of the two images of `A ⟶ B` turns the factorisation into the two identities. -/
private lemma isIso_app_of_factor {S T : 𝒜 ⥤ ℬ} (τ : S ⟶ T) {A B : 𝒜} (u : A ⟶ B)
    (hB : IsIso (τ.app B)) (k : T.obj A ⟶ S.obj A)
    (hk : k ≫ S.map u = T.map u ≫ inv (τ.app B))
    (hSu : Mono (S.map u)) (hTu : Mono (T.map u)) : IsIso (τ.app A) := by
  have := hB
  have := hSu
  have := hTu
  refine ⟨k, ?_, ?_⟩
  · refine (cancel_mono (S.map u)).mp ?_
    rw [Category.assoc, hk, ← τ.naturality_assoc u]
    simp
  · refine (cancel_mono (T.map u)).mp ?_
    rw [Category.assoc, ← τ.naturality u, ← Category.assoc, hk, Category.assoc]
    simp

end Abstract

/-! ### The unit of the adjunction along a surjection -/

section Unit

/-- **For a surjective morphism of schemes the unit `A ⟶ f_* f^{-1} A` of the
inverse-image/direct-image adjunction on abelian sheaves of the small étale sites is a
monomorphism.**  This is
`Stacks.EtaleCohomology.mono_smallEtaleUnitAb_of_surjective` carried from the adjunction with
the abstract inverse image to the adjunction
`Stacks.EtaleCohomology.etaleAbelianInverseImageDirectImageAdj` with the inverse image built as
a left Kan extension; the two have the same right adjoint, so their units differ by an
isomorphism.

This is the one place where surjectivity of `f` is used, and it is what the hypothesis `hunit`
of `Stacks.EtaleCohomology.isIso_etaleAbelianBaseChange_of_mono_unit` asks for. -/
public theorem mono_etaleAbelianUnit_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    (A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Mono ((etaleAbelianInverseImageDirectImageAdj.{u, 0} f).unit.app A) :=
  mono_of_comp_eq (Adjunction.unit_leftAdjointUniq_hom_app
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} f) (smallEtaleAdjunctionAb f) A)
    (mono_smallEtaleUnitAb_of_surjective f A)

end Unit

/-! ### Left exactness of the base change comparison -/

section LeftExact

variable {Y Z Y' Z' : Scheme.{u}} (g : Y ⟶ Z) (c : Z' ⟶ Z) (d : Y' ⟶ Y) (g' : Y' ⟶ Z')
  (sq₁ : d ≫ g = g' ≫ c)

/-- **The comparison of the square is invertible at a subobject of an object at which it is
invertible, provided it is monomorphic at the quotient.**  Both the source `g_* ⋙ c^{-1}` and
the target `d^{-1} ⋙ g'_*` of the comparison are left exact, so the source carries the kernel
presentation of `A` inside `B` to a kernel presentation; the composite of the target's `A ⟶ B`
with the inverse at `B` is killed by the map to the cokernel because the comparison is
monomorphic there, so it factors, and the factorisation is the inverse. -/
private lemma isIso_etaleAbelianBaseChange_app_of_mono_cokernel
    {A B : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (u : A ⟶ B) (hu : Mono u)
    (hB : IsIso ((etaleAbelianBaseChange.{u, v} g c d g' sq₁).app B))
    (hC : Mono ((etaleAbelianBaseChange.{u, v} g c d g' sq₁).app (cokernel u))) :
    IsIso ((etaleAbelianBaseChange.{u, v} g c d g' sq₁).app A) := by
  have := hu
  have := hB
  have := hC
  have hSlim : IsLimit ((KernelFork.ofι u (cokernel.condition u)).map
      (etaleAbelianDirectImage.{u, v} g ⋙ etaleAbelianInverseImage.{u, v} c)) :=
    KernelFork.mapIsLimit _ (Abelian.monoIsKernelOfCokernel
      (CokernelCofork.ofπ (cokernel.π u) (cokernel.condition u)) (cokernelIsCokernel u)) _
  have hnat := (etaleAbelianBaseChange.{u, v} g c d g' sq₁).naturality (cokernel.π u)
  have hw : ((etaleAbelianInverseImage.{u, v} d ⋙
          etaleAbelianDirectImage.{u, v} g').map u ≫
        inv ((etaleAbelianBaseChange.{u, v} g c d g' sq₁).app B)) ≫
      (etaleAbelianDirectImage.{u, v} g ⋙
        etaleAbelianInverseImage.{u, v} c).map (cokernel.π u) = 0 := by
    refine (cancel_mono ((etaleAbelianBaseChange.{u, v} g c d g' sq₁).app (cokernel u))).mp ?_
    rw [Category.assoc, hnat, Category.assoc, IsIso.inv_hom_id_assoc, ← Functor.map_comp,
      cokernel.condition, Functor.map_zero, zero_comp]
  exact isIso_app_of_factor (etaleAbelianBaseChange.{u, v} g c d g' sq₁) u hB
    (hSlim.lift (KernelFork.ofι _ hw)) (hSlim.fac _ WalkingParallelPair.zero)
    inferInstance inferInstance

end LeftExact

/-! ### Cancelling the surjection -/

section Main

variable {X Y Z X' Y' Z' : Scheme.{u}}

/-- **The comparison of the lower square is invertible at a direct image along `f`.**  This is
the cancellation of `Stacks.EtaleCohomology.etaleAbelianBaseChange_compDirectImage_app`: the
comparison of the rectangle at `F` factors as an isomorphism, the comparison of the lower square
at `f_* F`, `g'_*` of the comparison of the upper square at `F`, and an isomorphism, so the
middle factor is invertible as soon as the rectangle and the upper square are. -/
public theorem isIso_etaleAbelianBaseChange_directImage_of_compDirectImage
    (f : X ⟶ Y) (g : Y ⟶ Z) (gf : X ⟶ Z) (hgf : gf = f ≫ g)
    (c : Z' ⟶ Z) (d : Y' ⟶ Y) (g' : Y' ⟶ Z') (e : X' ⟶ X) (f' : X' ⟶ Y')
    (q : X' ⟶ Z') (hq : q = f' ≫ g')
    (sq₁ : d ≫ g = g' ≫ c) (sq₂ : e ≫ f = f' ≫ d) (hyp : e ≫ gf = q ≫ c)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (h₁ : IsIso ((etaleAbelianBaseChange.{u, v} f d e f' sq₂).app F))
    (h₂ : IsIso ((etaleAbelianBaseChange.{u, v} gf c e q hyp).app F)) :
    IsIso ((etaleAbelianBaseChange.{u, v} g c d g' sq₁).app
      ((etaleAbelianDirectImage.{u, v} f).obj F)) := by
  have := h₁
  refine isIso_of_comp_four_eq _ _ _ _ _
    (etaleAbelianBaseChange_compDirectImage_app.{u, v} f g gf hgf c d g' e f' q hq
      sq₁ sq₂ hyp F) inferInstance inferInstance inferInstance h₂

/-- **Stacks 0A4C in degree zero: cancelling a surjection from a composite.**  Let `f : X ⟶ Y`
and `g : Y ⟶ Z` be morphisms of schemes with named composite `gf : X ⟶ Z`, let `c : Z' ⟶ Z`, and
consider commutative squares
```
X' --e--> X      Y' --d--> Y
|f'       |f     |g'       |g
v         v      v         v
Y' --d--> Y      Z' --c--> Z
```
with `q : X' ⟶ Z'` the named composite of `f'` and `g'`.  Assume

1. the comparison `d^{-1} f_* ⟶ f'_* e^{-1}` of the upper square is invertible at every abelian
   sheaf on `X_étale`;
2. the comparison `c^{-1} (gf)_* ⟶ q_* e^{-1}` of the rectangle is invertible at every abelian
   sheaf on `X_étale`;
3. the unit `A ⟶ f_* f^{-1} A` is a monomorphism for every abelian sheaf `A` on `Y_étale`.

Then the comparison `c^{-1} g_* ⟶ g'_* d^{-1}` of the lower square is invertible at every
abelian sheaf on `Y_étale`.

Hypothesis 3 is what surjectivity of `f` provides:
`Stacks.EtaleCohomology.mono_etaleAbelianUnit_of_surjective` proves it from `Surjective f` at
the coefficients `Ab.{u + 1}`.  Properness of `f` and `g` is not used. -/
@[stacks 0A4C "RESTRICTED: degree zero only — each `cohomology commutes with base change` is \
invertibility of the underived comparison of Tag 0A2A at every abelian sheaf, not of the derived \
comparison at every torsion sheaf, the bridge between the two being Tag 0A4B, absent here; \
hypothesis (3) is carried as monomorphy of the unit `A ⟶ f_*f⁻¹A`, which \
`mono_etaleAbelianUnit_of_surjective` supplies from `Surjective f`; properness is unused"]
public theorem isIso_etaleAbelianBaseChange_of_mono_unit
    (f : X ⟶ Y) (g : Y ⟶ Z) (gf : X ⟶ Z) (hgf : gf = f ≫ g)
    (c : Z' ⟶ Z) (d : Y' ⟶ Y) (g' : Y' ⟶ Z') (e : X' ⟶ X) (f' : X' ⟶ Y')
    (q : X' ⟶ Z') (hq : q = f' ≫ g')
    (sq₁ : d ≫ g = g' ≫ c) (sq₂ : e ≫ f = f' ≫ d) (hyp : e ≫ gf = q ≫ c)
    (hunit : ∀ A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
      Mono ((etaleAbelianInverseImageDirectImageAdj.{u, v} f).unit.app A))
    (h₁ : ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
      IsIso ((etaleAbelianBaseChange.{u, v} f d e f' sq₂).app F))
    (h₂ : ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
      IsIso ((etaleAbelianBaseChange.{u, v} gf c e q hyp).app F))
    (A : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsIso ((etaleAbelianBaseChange.{u, v} g c d g' sq₁).app A) := by
  have key : ∀ A' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
      ∃ (B : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (w : A' ⟶ B), Mono w ∧
        IsIso ((etaleAbelianBaseChange.{u, v} g c d g' sq₁).app B) := by
    intro A'
    refine ⟨(etaleAbelianDirectImage.{u, v} f).obj
      ((etaleAbelianInverseImage.{u, v} f).obj A'),
      (etaleAbelianInverseImageDirectImageAdj.{u, v} f).unit.app A', hunit A', ?_⟩
    exact isIso_etaleAbelianBaseChange_directImage_of_compDirectImage.{u, v} f g gf hgf c d g'
      e f' q hq sq₁ sq₂ hyp ((etaleAbelianInverseImage.{u, v} f).obj A')
      (h₁ ((etaleAbelianInverseImage.{u, v} f).obj A'))
      (h₂ ((etaleAbelianInverseImage.{u, v} f).obj A'))
  have hmono : ∀ A' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
      Mono ((etaleAbelianBaseChange.{u, v} g c d g' sq₁).app A') := by
    intro A'
    obtain ⟨B, w, hw, hB⟩ := key A'
    have := hw
    exact mono_app_of_mono_map (etaleAbelianBaseChange.{u, v} g c d g' sq₁) w inferInstance hB
  obtain ⟨B, w, hw, hB⟩ := key A
  exact isIso_etaleAbelianBaseChange_app_of_mono_cokernel g c d g' sq₁ w hw hB (hmono _)

end Main

end Stacks.EtaleCohomology

end
