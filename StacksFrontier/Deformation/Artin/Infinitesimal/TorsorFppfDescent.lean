module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.CechExactFromSheaf
public import StacksFrontier.RingTheory.Descent.FaithfullyFlatModules

/-!
# Čech descent of a section of a sheaf of torsors along a faithfully flat covering

Let `F` be a sheaf of sets on a site, let `f : X ⟶ Y` be a morphism whose one-element presieve
`F` satisfies the sheaf condition for, and let

  `Z = X ×_Y X`,   `W = Z ×_X Z`

be the double and triple overlaps, with the two projections `p₀, p₁ : Z ⟶ X` and the three
projections `q₀, q₁, q₂ : W ⟶ Z`. Suppose the three values `F(X)`, `F(Z)`, `F(W)` are torsors
under abelian groups `G₀`, `G₁`, `G₂` and the five restriction maps are equivariant along
`d₀, d₁ : G₀ →+ G₁` and `e₀, e₁, e₂ : G₁ →+ G₂`. Then for a section `z` of `F` over `X` the
discrepancy `δ = F(p₁)(z) -ᵥ F(p₀)(z)` of its two restrictions to `Z` is a Čech `1`-cocycle,

  `e₂ δ - e₁ δ + e₀ δ = 0`,

and if every such cocycle is a coboundary `d₁ a - d₀ a` then `z` can be corrected so that its two
restrictions to `Z` agree, whence `F(Y)` is nonempty. When the covering is `Spec B' → Spec A'`
for a faithfully flat `A'`-algebra `B'` and the three groups are the base changes of one module
along `A' → B'`, `A' → B'₁`, `A' → B'₂`, the cocycle condition does force a coboundary; that is
the second half of this file, and it is faithful flatness that supplies it.

This is the computation the proof of [Stacks, Tag 0DNU] leaves out ("an omitted computation shows
`δ₁` is a 1-cocycle in the Čech complex") together with the step that consumes it. **No
`@[stacks 0DNU]` attribute is attached anywhere in this file, and none is earned**: Tag 0DNU
concludes the existence of a lift `x'` over `A'` of the object `x` of a deformation situation,
and reaching that conclusion from the content below needs two further inputs which this
development does not have, together with one compatibility of an input it does have.

* [Stacks, Tag 0DNS], that `B' ↦ {lifts of x|_{B' ⊗_{A'} A} to B'}/iso` is a sheaf on
  `(Aff/Spec A')_fppf`, which is what supplies the sheaf hypothesis here. The *functor* is available
  and at the right site: `Deformation.Artin.liftAlongSlicePresheaf` is stated for any fibred
  category over a base with fibre products, and the big affine fppf site over `S` has them by
  `AlgebraicGeometry.hasPullbacks_bigAffineFppf`. What is missing is only its sheaf property: no
  declaration in the library has that presheaf — or any other presheaf of isomorphism classes of
  lifts — as a sheaf for any topology. 0DNS is proved in the source from the base change of `Inf`
  of [Stacks, Tag 0DNR], and the library's 0DNR,
  `Deformation.Artin.existsUnique_infFlatBaseChange`, supplies that base change only granted
  `Deformation.Artin.InfHomRepresentation`, for which the library has no producer.
* [Stacks, Tag 0DNT] in the form the Čech argument consumes, namely a base-change isomorphism
  `T_x(M) ⊗_A B = T_y(M ⊗_A B)` that is compatible with the action of Tag 07Y9 (2)(b) on lifts.
  The library's 0DNT, `Deformation.Artin.existsUnique_tangentFlatBaseChange`, characterises its
  isomorphism only through the assumed `Deformation.Artin.TangentHomRepresentation`, so it says
  nothing about lifts and cannot serve as the equivariance hypothesis above.
* The compatibility of the [Stacks, Tag 07YA] *ring* base-change transitions with the action on
  lifts. The transitions themselves are proved: the tangent one is
  `Deformation.Artin.existsUnique_tangentBaseChange` of
  `StacksFrontier/Deformation/Artin/Obstruction/TangentPullback.lean`, and the companion one on
  infinitesimal automorphisms is `Deformation.Artin.existsUnique_infAutBaseChangeHom` of
  `StacksFrontier/Deformation/Artin/Obstruction/InfAutBaseChangeMap.lean`. What the equivariance
  hypotheses `hp₀`–`hq₂` below ask for is neither map but the second commuting square of
  Tag 07YA, the compatibility with the action of Tag 07Y9 (2)(b), and that square is not
  covered: by `Deformation.Artin.ActionOnLiftsData.action_difference_eq` and
  `Deformation.Artin.ActionOnLiftsData.difference_eq_of_action` the action and the difference
  determine one another, so it needs the transport along the ring map of
  `Deformation.Artin.IsGeometricDifference` and `Deformation.Artin.IsGeometricInfDifference`,
  which is assumed rather than proved, as the hypothesis `hL` of
  `Deformation.Artin.ActionOnLiftsData.pull_action_of_difference`.

*Where this chain bottoms out, and what waits on it.* [Stacks, Tag 0DNZ] — a point of an
algebraic stack smooth over `T'` lifts across a first order thickening `T ⟶ T'` of affine
schemes — is registered nowhere in the library, in neither the `@[stacks]` attribute form nor
the `add_to_stacks` form, and its only route is
Tag 0DNU: the source applies Tag 0DNU to descend the lift from the smooth surjective affine
`W' ⟶ T'` that it constructs. The rest of that proof is in hand, so Tag 0DNU is the whole of
what Tag 0DNZ waits on — Tag 057R `Stacks.Etale.exists_etale_lift_of_isClosedImmersion` extends
the étale `W ⟶ T` across the thickening, the appeal to Tag 04AM is made at the scheme atlas and
so is the unconditional `Stacks.Smooth.formallySmoothScheme_of_smooth`, Tag 06XH (2) is
`AlgebraicGeometry.Stack.exists_etaleCovering_fibre_lift_of_representable`, and Tag 0DNY, which
turns the conclusion into the dotted arrow of Tag 0H18, is
`AlgebraicGeometry.Stack.isFormallySmoothOnObjects_iff_nonempty_dottedArrow`.

Tag 0DNU and its input Tag 0DNS bottom out in the same place:
`Deformation.Artin.InfHomRepresentation`, which the library's Tag 0DNR
`Deformation.Artin.existsUnique_infFlatBaseChange` carries, and which has no producer — no def,
instance or theorem in the library concludes it. Three of its six fields cannot be filled from
anything in the library. `baseChangeQ`, `homRepX` and `homRepY` ask for a finitely presented
`A`-module `Q` with `Inf_x(M) = Hom_A(Q, M)` naturally in `M`, that is for `Q = e^*Ω_{G/A}` and the
representability of `Inf_x` by it, which is Tag 0617 and Tag 061C with Tags 05ZF and 05ZC for
the base change: no module standing for `e^*Ω_{G/A}` exists in the library, and no declaration
anywhere identifies `Inf_x`, or a tangent functor, with a `Hom`-module. The Tag 07YA transitions
named above do not supply these three, being maps *between* the two functors along `A ⟶ C` which
say nothing about representing either of them. The other three fields, `compatible`,
`restriction` and `restriction_isHomLift`, are only the data exhibiting `y` as `x|_{Spec C}`.

The torsor structure that Tag 0DNU puts on the set of lifts *is* available, as
`Deformation.Artin.exists_actionOnLifts` (Tag 07Y9 (2)(b)), and the acyclicity of the Čech
complex that Tag 0DNU quotes from [Stacks, Tag 03FJ] is available as
`Stacks.Descent.amitsurExtendedCochainComplex_acyclic_of_faithfullyFlat` (Tag 023M). Neither is
used below: the degree in which the cocycle lives here is `1`, and for a one-element covering
the vanishing of `H^1` is faithful flatness applied to the image of a single linear map, which
is `Module.Descent.mem_range_of_one_tmul_mem_range`.

## Main results

* `Deformation.Artin.sub_add_eq_zero_of_vsub_faces` — the Čech `1`-cocycle identity for the
  difference of the two restrictions of a section of a sheaf of torsors.
* `Deformation.Artin.map_vadd_eq_of_vsub_eq_sub` — correcting a section by a coboundary makes
  its two restrictions agree.
* `Deformation.Artin.nonempty_sections_of_cocycleBoundary` — the descent conclusion: if every
  cocycle is a coboundary, the sheaf has a section over the base of the covering.
* `Deformation.Artin.exists_sub_eq_of_faithfullyFlat` — for a faithfully flat base change whose
  tower identifies the three coefficient groups, every cocycle *is* a coboundary.
* `Deformation.Artin.nonempty_sections_of_faithfullyFlat` — the two combined.

## Implementation notes

The three overlaps enter as an abstract `CategoryTheory.IsPullback` square together with the
three face identities `q₀ ≫ p₀ = q₁ ≫ p₀`, `q₀ ≫ p₁ = q₂ ≫ p₀`, `q₁ ≫ p₁ = q₂ ≫ p₁`, rather
than as chosen fibre products: the application has them as spectra of tensor products, where the
projections are the ones the pushout squares of rings provide and not Lean's `pullback.fst`.

The equivariance of a restriction map is asked as `F(g)(a +ᵥ z) = (hom a) +ᵥ F(g)(z)` for an
additive homomorphism of the coefficient groups. Nothing requires the torsor structures to be
compatible with a module structure, which is why the first half of the file is stated for bare
`AddCommGroup`s; the module structures appear only in the second half, where faithful flatness is
used.

The sheaf condition is consumed through
`Stacks.CechSite.injective_and_exists_eq_of_isSheafFor_singleton`, which is exactly the
equalizer form of `CategoryTheory.Presieve.IsSheafFor` for a one-element presieve.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 057R](https://stacks.math.columbia.edu/tag/057R)
* [Stacks Project, Tag 05ZC](https://stacks.math.columbia.edu/tag/05ZC)
* [Stacks Project, Tag 05ZF](https://stacks.math.columbia.edu/tag/05ZF)
* [Stacks Project, Tag 0617](https://stacks.math.columbia.edu/tag/0617)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
* [Stacks Project, Tag 07YA](https://stacks.math.columbia.edu/tag/07YA)
* [Stacks Project, Tag 0DNR](https://stacks.math.columbia.edu/tag/0DNR)
* [Stacks Project, Tag 0DNS](https://stacks.math.columbia.edu/tag/0DNS)
* [Stacks Project, Tag 0DNT](https://stacks.math.columbia.edu/tag/0DNT)
* [Stacks Project, Tag 0DNU](https://stacks.math.columbia.edu/tag/0DNU)
* [Stacks Project, Tag 0DNZ](https://stacks.math.columbia.edu/tag/0DNZ)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped TensorProduct

namespace Deformation.Artin

universe u v w

section Cocycle

variable {G₀ G₁ G₂ : Type*} [AddCommGroup G₀] [AddCommGroup G₁] [AddCommGroup G₂]

/-- An equivariant map of torsors carries a difference of points to the difference of their
images. -/
private lemma map_vsub_of_vadd_eq {P Q : Type*} [AddTorsor G₀ P] [AddTorsor G₁ Q]
    (f : P → Q) (g : G₀ →+ G₁) (hf : ∀ a x, f (a +ᵥ x) = g a +ᵥ f x) (x y : P) :
    g (x -ᵥ y) = f x -ᵥ f y := by
  calc
    g (x -ᵥ y) = (g (x -ᵥ y) +ᵥ f y) -ᵥ f y := (vadd_vsub _ _).symm
    _ = f x -ᵥ f y := by rw [← hf, vsub_vadd]

/-- **The Čech `1`-cocycle identity for the difference of two restrictions.**

For maps `p₀, p₁ : P → Q` and `q₀, q₁, q₂ : Q → R` of torsors, equivariant along
`e₀, e₁, e₂` on the second stage and satisfying the three face identities of a Čech complex, the
difference `p₁ z -ᵥ p₀ z` of the two restrictions of a point `z` is annihilated by the
alternating sum `e₂ - e₁ + e₀`. -/
public theorem sub_add_eq_zero_of_vsub_faces
    {P Q R : Type*} [AddTorsor G₁ Q] [AddTorsor G₂ R]
    (p₀ p₁ : P → Q) (q₀ q₁ q₂ : Q → R) (e₀ e₁ e₂ : G₁ →+ G₂)
    (hq₀ : ∀ a x, q₀ (a +ᵥ x) = e₀ a +ᵥ q₀ x)
    (hq₁ : ∀ a x, q₁ (a +ᵥ x) = e₁ a +ᵥ q₁ x)
    (hq₂ : ∀ a x, q₂ (a +ᵥ x) = e₂ a +ᵥ q₂ x)
    (h₀₁ : ∀ z, q₀ (p₀ z) = q₁ (p₀ z))
    (h₀₂ : ∀ z, q₀ (p₁ z) = q₂ (p₀ z))
    (h₁₂ : ∀ z, q₁ (p₁ z) = q₂ (p₁ z)) (z : P) :
    e₂ (p₁ z -ᵥ p₀ z) - e₁ (p₁ z -ᵥ p₀ z) + e₀ (p₁ z -ᵥ p₀ z) = 0 := by
  rw [map_vsub_of_vadd_eq q₀ e₀ hq₀, map_vsub_of_vadd_eq q₁ e₁ hq₁,
    map_vsub_of_vadd_eq q₂ e₂ hq₂, h₀₁, h₀₂, h₁₂]
  calc
    _ = (q₂ (p₁ z) -ᵥ q₂ (p₀ z) + (q₂ (p₀ z) -ᵥ q₁ (p₀ z))) -
        (q₂ (p₁ z) -ᵥ q₁ (p₀ z)) := by abel
    _ = 0 := by rw [vsub_add_vsub_cancel, sub_self]

/-- **Correcting a point by a coboundary makes its two images agree.**

If the difference of the two images of `z` is the coboundary `d₁ a - d₀ a`, then translating `z`
by `-a` equalizes them. -/
public theorem map_vadd_eq_of_vsub_eq_sub
    {P Q : Type*} [AddTorsor G₀ P] [AddTorsor G₁ Q]
    (p₀ p₁ : P → Q) (d₀ d₁ : G₀ →+ G₁)
    (hp₀ : ∀ a x, p₀ (a +ᵥ x) = d₀ a +ᵥ p₀ x)
    (hp₁ : ∀ a x, p₁ (a +ᵥ x) = d₁ a +ᵥ p₁ x)
    (z : P) (a : G₀) (ha : d₁ a - d₀ a = p₁ z -ᵥ p₀ z) :
    p₀ ((-a) +ᵥ z) = p₁ ((-a) +ᵥ z) := by
  refine (vsub_eq_zero_iff_eq.mp ?_).symm
  rw [hp₀, hp₁, vadd_vsub_vadd_comm, map_neg, map_neg, ← ha]
  abel

end Cocycle

section SheafDescent

variable {G₀ G₁ G₂ : Type*} [AddCommGroup G₀] [AddCommGroup G₁] [AddCommGroup G₂]

/-- **The descent step of the proof of [Stacks, Tag 0DNU].**

Let `F` be a presheaf satisfying the sheaf condition for the one-element presieve of
`f : X ⟶ Y`, let `p₀, p₁ : Z ⟶ X` exhibit `Z` as `X ×_Y X`, and let `q₀, q₁, q₂ : W ⟶ Z`
satisfy the three face identities. If the three values of `F` are torsors whose restriction maps
are equivariant, and every Čech `1`-cocycle in `G₁` is a coboundary, then `F` has a section over
`Y`.

This is the final step of the proof of Tag 0DNU, with the two inputs the source quotes — the
sheaf property of Tag 0DNS and the identification of the coefficients through Tag 0DNT — as
hypotheses. See the module documentation: no `@[stacks 0DNU]` attribute is earned. -/
public theorem nonempty_sections_of_cocycleBoundary
    {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w}
    {X Y Z W : C} (f : X ⟶ Y)
    (hf : Presieve.IsSheafFor F (Presieve.singleton f))
    (p₀ p₁ : Z ⟶ X) (hpb : IsPullback p₀ p₁ f f)
    (q₀ q₁ q₂ : W ⟶ Z)
    (h₀₁ : q₀ ≫ p₀ = q₁ ≫ p₀) (h₀₂ : q₀ ≫ p₁ = q₂ ≫ p₀) (h₁₂ : q₁ ≫ p₁ = q₂ ≫ p₁)
    [AddTorsor G₀ (F.obj (op X))] [AddTorsor G₁ (F.obj (op Z))] [AddTorsor G₂ (F.obj (op W))]
    (d₀ d₁ : G₀ →+ G₁) (e₀ e₁ e₂ : G₁ →+ G₂)
    (hp₀ : ∀ a z, F.map p₀.op (a +ᵥ z) = d₀ a +ᵥ F.map p₀.op z)
    (hp₁ : ∀ a z, F.map p₁.op (a +ᵥ z) = d₁ a +ᵥ F.map p₁.op z)
    (hq₀ : ∀ a z, F.map q₀.op (a +ᵥ z) = e₀ a +ᵥ F.map q₀.op z)
    (hq₁ : ∀ a z, F.map q₁.op (a +ᵥ z) = e₁ a +ᵥ F.map q₁.op z)
    (hq₂ : ∀ a z, F.map q₂.op (a +ᵥ z) = e₂ a +ᵥ F.map q₂.op z)
    (hexact : ∀ t : G₁, e₂ t - e₁ t + e₀ t = 0 → ∃ a : G₀, d₁ a - d₀ a = t) :
    Nonempty (F.obj (op Y)) := by
  obtain ⟨z⟩ := (inferInstance : Nonempty (F.obj (op X)))
  have hc := sub_add_eq_zero_of_vsub_faces
    (F.map p₀.op) (F.map p₁.op) (F.map q₀.op) (F.map q₁.op) (F.map q₂.op) e₀ e₁ e₂ hq₀ hq₁ hq₂
    (fun t => by simp only [← Functor.map_comp_apply, ← op_comp, h₀₁])
    (fun t => by simp only [← Functor.map_comp_apply, ← op_comp, h₀₂])
    (fun t => by simp only [← Functor.map_comp_apply, ← op_comp, h₁₂]) z
  obtain ⟨a, ha⟩ := hexact _ hc
  obtain ⟨-, hiff⟩ :=
    Stacks.CechSite.injective_and_exists_eq_of_isSheafFor_singleton f p₀ p₁ hf hpb
  obtain ⟨t, -⟩ := (hiff _).mp
    (map_vadd_eq_of_vsub_eq_sub (F.map p₀.op) (F.map p₁.op) d₀ d₁ hp₀ hp₁ z a ha)
  exact ⟨t⟩

end SheafDescent

section FaithfullyFlat

/-- **Every Čech `1`-cocycle is a coboundary, for a faithfully flat base change.**

Let `S` be a faithfully flat `R`-algebra, let `G₀` be an `R`-module and let `G₁`, `G₂` be
`S`-modules identified with `S ⊗_R G₀` and `S ⊗_R G₁` by `E₀` and `E₁`, the identifications being
pinned on the generators `1 ⊗ m` by `d₁` and `e₂`. If `e₀` and `e₁` agree with `e₂` on the image
of `d₁` in the two ways a Čech complex requires, then every `z` with `e₂ z - e₁ z + e₀ z = 0` is
of the form `d₁ a - d₀ a`.

The proof is faithful flatness applied once: the element `1 ⊗ z` of `S ⊗_R G₁` lies in the image
of the base change of `d₁ - d₀`, so `z` lies in the image of `d₁ - d₀` itself by
`Module.Descent.mem_range_of_one_tmul_mem_range`. -/
public theorem exists_sub_eq_of_faithfullyFlat
    {R S G₀ G₁ G₂ : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    [AddCommGroup G₀] [Module R G₀]
    [AddCommGroup G₁] [Module R G₁] [Module S G₁] [IsScalarTower R S G₁]
    [AddCommGroup G₂] [Module R G₂] [Module S G₂] [IsScalarTower R S G₂]
    (d₀ d₁ : G₀ →ₗ[R] G₁) (e₀ e₁ : G₁ →ₗ[S] G₂) (e₂ : G₁ →ₗ[R] G₂)
    (E₀ : (S ⊗[R] G₀) ≃ₗ[S] G₁) (E₁ : (S ⊗[R] G₁) ≃ₗ[S] G₂)
    (hE₀ : ∀ m, E₀ ((1 : S) ⊗ₜ[R] m) = d₁ m)
    (hE₁ : ∀ m, E₁ ((1 : S) ⊗ₜ[R] m) = e₂ m)
    (h₀₂ : ∀ m, e₀ (d₁ m) = e₂ (d₀ m))
    (h₁₂ : ∀ m, e₁ (d₁ m) = e₂ (d₁ m))
    (z : G₁) (hz : e₂ z - e₁ z + e₀ z = 0) :
    ∃ a : G₀, d₁ a - d₀ a = z := by
  have hcompat (d : G₀ →ₗ[R] G₁) (e : G₁ →ₗ[S] G₂) (hc : ∀ m, e (d₁ m) = e₂ (d m)) :
      E₁.toLinearMap ∘ₗ TensorProduct.AlgebraTensorModule.lTensor S S d =
        e ∘ₗ E₀.toLinearMap := by
    ext m
    change E₁ ((1 : S) ⊗ₜ[R] d m) = e (E₀ ((1 : S) ⊗ₜ[R] m))
    rw [hE₀, hE₁]
    exact (hc m).symm
  have hboundary : (1 : S) ⊗ₜ[R] z ∈
      LinearMap.range (LinearMap.lTensor S (d₁ - d₀)) := by
    refine ⟨E₀.symm z, ?_⟩
    apply E₁.injective
    rw [hE₁]
    have h₀ := LinearMap.congr_fun (hcompat d₀ e₀ h₀₂) (E₀.symm z)
    have h₁ := LinearMap.congr_fun (hcompat d₁ e₁ h₁₂) (E₀.symm z)
    change E₁ (LinearMap.lTensor S d₀ (E₀.symm z)) = e₀ (E₀ (E₀.symm z)) at h₀
    change E₁ (LinearMap.lTensor S d₁ (E₀.symm z)) = e₁ (E₀ (E₀.symm z)) at h₁
    rw [LinearEquiv.apply_symm_apply] at h₀ h₁
    rw [LinearMap.lTensor_sub, LinearMap.sub_apply, map_sub, h₁, h₀]
    calc
      e₁ z - e₀ z = e₂ z - (e₂ z - e₁ z + e₀ z) := by abel
      _ = e₂ z := by rw [hz, sub_zero]
  exact Module.Descent.mem_range_of_one_tmul_mem_range R S (d₁ - d₀) hboundary

/-- **The descent step of [Stacks, Tag 0DNU], with its cocycle hypothesis discharged.**

`Deformation.Artin.nonempty_sections_of_cocycleBoundary` and
`Deformation.Artin.exists_sub_eq_of_faithfullyFlat` combined: for a sheaf of torsors on a
one-element covering whose coefficient groups are the base changes of one module along a
faithfully flat ring map, the sheaf has a section over the base of the covering.

In Tag 0DNU the covering is `Spec B' → Spec A'` for a faithfully flat finitely presented
`A'`-algebra `B'`, the sheaf is the one of Tag 0DNS, and the coefficient groups are
`T_x(I) ⊗_A B`, `T_x(I) ⊗_A B₁`, `T_x(I) ⊗_A B₂`, identified as base changes by Tag 0DNT.
See the module documentation: none of those three inputs is available in this library, and no
`@[stacks 0DNU]` attribute is earned. -/
public theorem nonempty_sections_of_faithfullyFlat
    {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w}
    {X Y Z W : C} (f : X ⟶ Y)
    (hf : Presieve.IsSheafFor F (Presieve.singleton f))
    (p₀ p₁ : Z ⟶ X) (hpb : IsPullback p₀ p₁ f f)
    (q₀ q₁ q₂ : W ⟶ Z)
    (hface₀₁ : q₀ ≫ p₀ = q₁ ≫ p₀) (hface₀₂ : q₀ ≫ p₁ = q₂ ≫ p₀)
    (hface₁₂ : q₁ ≫ p₁ = q₂ ≫ p₁)
    {R S G₀ G₁ G₂ : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S]
    [AddCommGroup G₀] [Module R G₀]
    [AddCommGroup G₁] [Module R G₁] [Module S G₁] [IsScalarTower R S G₁]
    [AddCommGroup G₂] [Module R G₂] [Module S G₂] [IsScalarTower R S G₂]
    [AddTorsor G₀ (F.obj (op X))] [AddTorsor G₁ (F.obj (op Z))] [AddTorsor G₂ (F.obj (op W))]
    (d₀ d₁ : G₀ →ₗ[R] G₁) (e₀ e₁ : G₁ →ₗ[S] G₂) (e₂ : G₁ →ₗ[R] G₂)
    (E₀ : (S ⊗[R] G₀) ≃ₗ[S] G₁) (E₁ : (S ⊗[R] G₁) ≃ₗ[S] G₂)
    (hE₀ : ∀ m, E₀ ((1 : S) ⊗ₜ[R] m) = d₁ m)
    (hE₁ : ∀ m, E₁ ((1 : S) ⊗ₜ[R] m) = e₂ m)
    (hcompat₀ : ∀ m, e₀ (d₁ m) = e₂ (d₀ m))
    (hcompat₁ : ∀ m, e₁ (d₁ m) = e₂ (d₁ m))
    (hp₀ : ∀ a z, F.map p₀.op (a +ᵥ z) = d₀ a +ᵥ F.map p₀.op z)
    (hp₁ : ∀ a z, F.map p₁.op (a +ᵥ z) = d₁ a +ᵥ F.map p₁.op z)
    (hq₀ : ∀ a z, F.map q₀.op (a +ᵥ z) = e₀ a +ᵥ F.map q₀.op z)
    (hq₁ : ∀ a z, F.map q₁.op (a +ᵥ z) = e₁ a +ᵥ F.map q₁.op z)
    (hq₂ : ∀ a z, F.map q₂.op (a +ᵥ z) = e₂ a +ᵥ F.map q₂.op z) :
    Nonempty (F.obj (op Y)) :=
  nonempty_sections_of_cocycleBoundary f hf p₀ p₁ hpb q₀ q₁ q₂
    hface₀₁ hface₀₂ hface₁₂ d₀.toAddMonoidHom d₁.toAddMonoidHom
    e₀.toAddMonoidHom e₁.toAddMonoidHom e₂.toAddMonoidHom hp₀ hp₁ hq₀ hq₁ hq₂
    (fun _ ht => exists_sub_eq_of_faithfullyFlat d₀ d₁ e₀ e₁ e₂ E₀ E₁ hE₀ hE₁
      hcompat₀ hcompat₁ _ ht)

end FaithfullyFlat

end Deformation.Artin

end
