module

public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafPushforwardNormal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorSheafSecondMap
import StacksCore.Tactic.StacksAttribute

/-!
# The right-hand exactness of the fundamental exact sequence of Stacks 03RI

Let `X` be a smooth curve over a field `k`, with generic point `η`, function field `K` and
inclusion `j : Spec K ⟶ X`. The second map of the fundamental exact sequence of Stacks 03RI,
`0 → 𝐆_{m,X} → j_* 𝐆_{m,η} → ⨁_{x ∈ X_0} (i_x)_* 𝐙 → 0`,
is constructed in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorSheafSecondMap`. This
file proves that it is an **epimorphism**, which is the exactness of the sequence at its right
end.

## Main results

* `Stacks.EtaleCohomology.epi_divisorSequenceSecondMapOfCurve`: **the second map of the
  fundamental exact sequence of Stacks 03RI is an epimorphism** for a smooth curve over a field.
* `Stacks.EtaleCohomology.imageSieve_ι_mem_of_isCurve`: the local statement it reduces to — a
  section of a single summand `(i_x)_* 𝐙` over an arbitrary étale `X`-scheme is, étale locally,
  the divisor of a section of `j_* 𝐆_{m,η}`.
* `Stacks.EtaleCohomology.exists_affineEtale_isIntegral`: **the shrinking** — every open of an
  étale `X`-scheme contains, around any of its points, the image of an *integral affine* étale
  `X`-scheme, under an open immersion over `X`.
* `Stacks.EtaleCohomology.integerSkyscraperDivisorOfPoint_eq_of_forall`: a section of
  `(i_x)_* 𝐙` is the image of a unit on the generic fibre as soon as the orders of vanishing
  match pointwise on the fibre over `x`.

## Implementation notes

**The shape of the argument.** `Stacks.EtaleCohomology.epi_divisorSequenceSecondMap_of_forall_`
`imageSieve_ι_mem` reduces the epimorphism to one summand at a time: for a closed point `x`, an
étale `X`-scheme `U` and a section `t` of `(i_x)_* 𝐙` over `U`, the arrows along which the image
of `t` under the summand inclusion restricts into the image of the second map must cover `U`. The
covering family is indexed by the points of `U`, and around each point `w` of `U` the member is
built in two shrinkings, each by `Stacks.EtaleCohomology.exists_affineEtale_isIntegral`:

* the first produces an integral affine étale `X`-scheme `P` inside an open `D` on which the
  fibre over `x` has at most the one point `w`, so that the fibre of `P` over `x` is a
  subsingleton by `Stacks.EtaleCohomology.subsingleton_pullback_fromSpecResidueField`, and the
  section of `(i_x)_* 𝐙` over `P` is therefore determined by a single integer;
* the second shrinks `P` to the neighbourhood on which the rational function produced by
  `Stacks.EtaleCohomology.exists_etaleGenericFibreOrdOfPoint_eq_and_forall_eq_zero` has no zeros
  and no poles away from that one point, so that its family of orders of vanishing is supported
  at `x` alone and `Stacks.EtaleCohomology.closedPointDivisorSheaf.sheafSectionOfDirectSum_eq_ι`
  identifies it with the summand inclusion of its member at `x`.

**Why no transport of the section along the second shrinking is needed, and hence no naturality
of `Stacks.EtaleCohomology.integerSkyscraperSectionsIsoLocallyConstantMaps`.** The prescribed
order of vanishing is asked for *before* the second shrinking, where the integer to be prescribed
is not yet known: the integer is read off the section restricted to the *shrunk* scheme. The
circularity is broken by prescribing the order `1` instead, and then using the integer multiple
of the resulting section in the additive group `Additive (Γ(η ×_X P, 𝒪^*)ˣ)`: the order of
vanishing is a homomorphism, so a multiple of a function with divisor `y` has divisor a multiple
of `y`, and the open on which the function has no other zeros and poles is unchanged. The second
shrinking is therefore chosen once and for all, and the integer afterwards. This is why the
naturality of the sections description of the constant sheaf, which the implementation notes of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorSheafSecondMap` record as
the missing transport, is not needed at all.

**The étale `X`-schemes are rebuilt, not restricted.** An object of
`AlgebraicGeometry.Scheme.AffineEtale` is a commutative ring `R` together with an étale
`Spec R ⟶ X`, so an affine open `A` of an étale `X`-scheme `U` is not an object of that category
until it is presented as one: `Stacks.EtaleCohomology.exists_affineEtale_of_isOpenImmersion` does
this with `AlgebraicGeometry.Scheme.isoSpec`, and returns the isomorphism with the original
scheme, along which integrality is transported by
`AlgebraicGeometry.IsIntegral.of_isIso`. The affine étale site is where the component of the
second map can be computed at all, by
`Stacks.EtaleCohomology.divisorSequenceSecondMap_hom_app`.

**What this does not prove.** Only the right-hand exactness. Together with
`Stacks.EtaleCohomology.mono_multiplicativeDirectImageComparison_genericPointInclusion`, the left
end, and
`Stacks.EtaleCohomology.multiplicativeDirectImageComparison_comp_divisorSequenceSecondMapOfCurve`,
that the sequence is a complex, what remains of Stacks 03RI is the exactness in the middle. That
is proved in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorMiddleExactness`, where
the four are assembled into the short exactness of the sequence,
`Stacks.EtaleCohomology.shortExact_divisorSequenceOfCurve`; so the short exactness hypothesis
`hSE` of `Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_smoothCurve` is not
discharged here, but it is discharged there.

## References

* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI): the fundamental exact
  sequence, Theorem 59.68.1. The source states it for a smooth curve over an algebraically closed
  field; the right-hand exactness is proved here for a smooth curve over an arbitrary field.
* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM): the vanishing theorem
  the sequence is needed for.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Order TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

attribute [local instance 10000] hasCoproduct_closedPointSkyscraper

/-- An étale scheme over a locally Noetherian scheme is locally Noetherian; see
`Stacks.EtaleCohomology.isLocallyNoetherian_etale_left`. -/
local instance isLocallyNoetherian_left_of_etale (X : Scheme.{u}) [IsLocallyNoetherian X]
    (U : X.Etale) : IsLocallyNoetherian U.left :=
  isLocallyNoetherian_etale_left X U

/-- An affine étale scheme over a locally Noetherian scheme has a Noetherian space; see
`Stacks.EtaleCohomology.noetherianSpace_affineEtale_left`. -/
local instance noetherianSpace_left_of_affineEtale (X : Scheme.{u}) [IsLocallyNoetherian X]
    (W : X.AffineEtale) : NoetherianSpace ((Scheme.AffineEtale.Spec X).obj W).left :=
  noetherianSpace_affineEtale_left X W

/-! ### A closed point of a curve is not its generic point -/

/-- **A closed point of a curve is not its generic point.** If the generic point were closed it
would be the only point, since every point is in the closure of the generic point; and a
one-point space has topological Krull dimension zero, not one.

This is the hypothesis under which the order of vanishing is defined, so it is what makes
`Stacks.EtaleCohomology.coheight_eq_one_of_etale_of_isCurve` applicable at a point of an étale
`X`-scheme lying over a closed point of the curve. -/
theorem ne_genericPoint_of_mem_closedPoints_of_isCurve {k : Type u} [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [IsCurve k g] (x : closedPoints X) : x.1 ≠ genericPoint X := by
  intro hx
  have hsub : ∀ z : X, z = x.1 := fun z => by
    have hsp : genericPoint X ⤳ z := genericPoint_specializes z
    rw [← hx] at hsp
    have hmem : z ∈ closure ({x.1} : Set X) := hsp.mem_closure
    rwa [(x.2 : IsClosed ({x.1} : Set X)).closure_eq, Set.mem_singleton_iff] at hmem
  have : Subsingleton ↥X := ⟨fun a b => (hsub a).trans (hsub b).symm⟩
  have h0 : topologicalKrullDim X = 0 := by
    rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso
      (irreducibleSetEquivPoints (α := (X : Type u)))]
    exact Order.krullDim_eq_zero
  rw [IsCurve.topologicalKrullDim_eq_one (k := k) (f := g)] at h0
  exact absurd h0 (by decide)

/-! ### Isolating a point in the fibre of an étale morphism over a closed point -/

/-- **A point of a scheme étale over another has an open neighbourhood meeting the fibre over a
closed point in at most that one point.** The fibres of an étale morphism are discrete, since an
étale morphism is locally quasi-finite by
`AlgebraicGeometry.locallyQuasiFinite_of_etale`, so a point of the fibre is open in it and hence
cut out by an open of the ambient scheme; a point *off* the fibre has the complement of the
fibre, which is open because the point of the target is closed.

This is what makes a section of `(i_x)_* 𝐙` over a sufficiently small étale `X`-scheme a single
integer, through
`Stacks.EtaleCohomology.subsingleton_pullback_fromSpecResidueField`. -/
theorem exists_opens_eq_of_etale_of_isClosed {X Z : Scheme.{u}} (q : Z ⟶ X) [Etale q] {x : X}
    (hx : IsClosed ({x} : Set X)) (w : Z) :
    ∃ D : Z.Opens, w ∈ D ∧ ∀ z ∈ D, q.base z = x → z = w := by
  have : LocallyQuasiFinite q := (locallyQuasiFinite_of_etale q).2
  by_cases hw : q.base w = x
  · have hd : DiscreteTopology ↥(q.base ⁻¹' {x}) :=
      (q.isDiscrete_preimage_singleton x).to_subtype
    obtain ⟨s, hs, hspec⟩ := isOpen_induced_iff.mp
      (isOpen_discrete ({(⟨w, hw⟩ : ↥(q.base ⁻¹' {x}))} : Set ↥(q.base ⁻¹' {x})))
    refine ⟨⟨s, hs⟩, ?_, fun z hz hzx => ?_⟩
    · have hmem : (⟨w, hw⟩ : ↥(q.base ⁻¹' {x})) ∈ Subtype.val ⁻¹' s := by rw [hspec]; rfl
      exact hmem
    · have hmem : (⟨z, hzx⟩ : ↥(q.base ⁻¹' {x})) ∈ Subtype.val ⁻¹' s := hz
      rw [hspec] at hmem
      exact congrArg Subtype.val hmem
  · exact ⟨⟨(q.base ⁻¹' {x})ᶜ, (hx.preimage q.continuous).isOpen_compl⟩, hw,
      fun z hz hzx => absurd hzx hz⟩

/-! ### Shrinking an étale `X`-scheme to an integral affine one -/

/-- **An affine scheme with an open immersion into an étale `X`-scheme, rebuilt as an object of
the affine étale site.** The objects of `AlgebraicGeometry.Scheme.AffineEtale` are commutative
rings with an étale structure morphism out of their spectrum, so the rebuilding goes through
`AlgebraicGeometry.Scheme.isoSpec`; the resulting isomorphism with the original scheme is part of
the statement, since it is what transports properties of that scheme to the new object. -/
theorem exists_affineEtale_of_isOpenImmersion {X : Scheme.{u}} (U : X.Etale) {Y : Scheme.{u}}
    [IsAffine Y] (h : Y ⟶ U.left) [IsOpenImmersion h] :
    ∃ (W : X.AffineEtale) (φ : (Scheme.AffineEtale.Spec X).obj W ⟶ U)
      (e : ((Scheme.AffineEtale.Spec X).obj W).left ≅ Y), e.hom ≫ h = φ.left := by
  have : Etale U.hom := U.prop
  have : Etale (Y.isoSpec.inv ≫ h ≫ U.hom) := inferInstance
  exact ⟨Scheme.AffineEtale.mk (Y.isoSpec.inv ≫ h ≫ U.hom),
    MorphismProperty.Over.homMk (Y.isoSpec.inv ≫ h) (Category.assoc _ _ _) trivial,
    Y.isoSpec.symm, rfl⟩

/-- **Every point of every open of an étale `X`-scheme is in the image of an integral affine
étale `X`-scheme mapping into that open.** This is the shrinking the right-hand exactness of
Stacks 03RI needs: the prescribed-divisor statement
`Stacks.EtaleCohomology.exists_etaleGenericFibreOrdOfPoint_eq_and_forall_eq_zero` requires the
étale `X`-scheme integral, and
`Stacks.EtaleCohomology.divisorSequenceSecondMap_hom_app` computes the second map only on affine
ones.

Integrality comes from `Stacks.EtaleCohomology.exists_isIntegral_open_of_etale` applied to the
open itself, which is étale over `X`; affineness from
`AlgebraicGeometry.exists_isAffineOpen_mem_and_subset` inside the integral open so produced, an
affine open of an integral scheme being integral as soon as it is nonempty; and the passage to an
object of the affine étale site from
`Stacks.EtaleCohomology.exists_affineEtale_of_isOpenImmersion`. -/
theorem exists_affineEtale_isIntegral {X : Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    [IsNormal X] (U : X.Etale) (Ω : U.left.Opens) {w : U.left} (hw : w ∈ Ω) :
    ∃ (W : X.AffineEtale) (φ : (Scheme.AffineEtale.Spec X).obj W ⟶ U),
      AlgebraicGeometry.IsIntegral ((Scheme.AffineEtale.Spec X).obj W).left ∧
        IsOpenImmersion φ.left ∧ w ∈ Set.range φ.left.base ∧
          Set.range φ.left.base ⊆ (Ω : Set U.left) := by
  have : Etale U.hom := U.prop
  have : AlgebraicGeometry.IsIntegral ((Functor.fromPUnit X).obj U.right) :=
    inferInstanceAs (AlgebraicGeometry.IsIntegral X)
  have : IsNormal ((Functor.fromPUnit X).obj U.right) := inferInstanceAs (IsNormal X)
  have : Etale (Ω.ι ≫ U.hom) := inferInstance
  obtain ⟨Z, s, hs, hZ, z₀, hz₀⟩ :=
    exists_isIntegral_open_of_etale (Ω.ι ≫ U.hom) (⟨w, hw⟩ : Ω.toScheme)
  have := hs
  have := hZ
  obtain ⟨A, hA, hz₀A, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : Z.Opens)) (x := z₀) trivial
  have : IsAffine A.toScheme := hA
  have : Nonempty A := ⟨⟨z₀, hz₀A⟩⟩
  have : AlgebraicGeometry.IsIntegral A.toScheme := inferInstance
  obtain ⟨W, φ, e, he⟩ := exists_affineEtale_of_isOpenImmersion U (A.ι ≫ s ≫ Ω.ι)
  have hoi : IsOpenImmersion φ.left := by rw [← he]; infer_instance
  have hinv : ∀ y : A.toScheme, e.hom.base (e.inv.base y) = y := fun y => by simp
  have ept : ∀ y : ((Scheme.AffineEtale.Spec X).obj W).left,
      φ.left.base y = Ω.ι.base (s.base (A.ι.base (e.hom.base y))) := fun y =>
    (congrArg (fun k : ((Scheme.AffineEtale.Spec X).obj W).left ⟶ U.left => k.base y)
        he).symm.trans
      (((Scheme.Hom.comp_apply e.hom (A.ι ≫ s ≫ Ω.ι) y).trans
        (Scheme.Hom.comp_apply A.ι (s ≫ Ω.ι) _)).trans (Scheme.Hom.comp_apply s Ω.ι _))
  refine ⟨W, φ, AlgebraicGeometry.IsIntegral.of_isIso e.inv, hoi,
    ⟨e.inv.base ⟨z₀, hz₀A⟩, ?_⟩, ?_⟩
  · exact (ept _).trans
      ((congrArg (fun z : A.toScheme => Ω.ι.base (s.base (A.ι.base z)))
          (hinv ⟨z₀, hz₀A⟩)).trans (congrArg Ω.ι.base hz₀))
  · rintro y ⟨q, rfl⟩
    exact Set.mem_of_eq_of_mem (ept q) (s.base (A.ι.base (e.hom.base q))).2

/-! ### The `x`-component of the second map, read through the sections of the constant sheaf -/

/-- **A section of `(i_x)_* 𝐙` over an étale `X`-scheme is the image of a unit on the generic
fibre as soon as their orders of vanishing agree at every point of the fibre over `x`.** The
`x`-component of the second map of Stacks 03RI is, by definition, the family of orders of
vanishing on the fibre read through the sections description of the constant sheaf, Stacks 03P5,
so an equality of sections of `(i_x)_* 𝐙` is an equality of locally constant `𝐙`-valued maps on
the fibre, hence pointwise.

This is the form in which the right-hand exactness of Stacks 03RI consumes the prescribed-divisor
statement: on a scheme whose fibre over `x` is a single point, the hypothesis is a single
equation of integers. -/
theorem integerSkyscraperDivisorOfPoint_eq_of_forall {X : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [IsNormal X] (U : X.Etale) [IsLocallyNoetherian U.left]
    (x : X) (a : Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ))
    (t : ToType ((integerSkyscraper.{u, v} X x).obj.obj (op U)))
    (h : ∀ p : ((smallEtaleBaseChange (X.fromSpecResidueField x)).obj U).left,
      etaleGenericFibreOrdOfPoint U ((pullback.fst U.hom (X.fromSpecResidueField x)) p) a =
        ((integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X x U).hom.hom t p).down) :
    integerSkyscraperDivisorOfPoint.{u, v} U x a = t := by
  have key : residueFibreOrdOfPoint.{u, v} U x a =
      (integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X x U).hom.hom t :=
    LocallyConstant.ext fun p => ULift.ext (h p)
  rw [integerSkyscraperDivisorOfPoint, AddMonoidHom.comp_apply, key]
  simp

/-- **A unit on the generic fibre with no zeros and no poles on the fibre over `x` has trivial
`x`-component.** This is
`Stacks.EtaleCohomology.integerSkyscraperDivisorOfPoint_eq_of_forall` at the zero section, and it
is what makes the family of orders of vanishing supported at a single closed point, so that
`Stacks.EtaleCohomology.closedPointDivisorSheaf.sheafSectionOfDirectSum_eq_ι` applies to it. -/
theorem integerSkyscraperDivisorOfPoint_eq_zero_of_forall {X : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [IsNormal X] (U : X.Etale) [IsLocallyNoetherian U.left]
    (x : X) (a : Additive ((Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ))
    (h : ∀ p : ((smallEtaleBaseChange (X.fromSpecResidueField x)).obj U).left,
      etaleGenericFibreOrdOfPoint U ((pullback.fst U.hom (X.fromSpecResidueField x)) p) a = 0) :
    integerSkyscraperDivisorOfPoint.{u, v} U x a = 0 := by
  rw [integerSkyscraperDivisorOfPoint, AddMonoidHom.comp_apply,
    show residueFibreOrdOfPoint.{u, v} U x a = 0 from
      LocallyConstant.ext fun p => ULift.ext (h p), map_zero]

/-! ### One member of the covering family -/

/-- A morphism of étale `X`-schemes commutes with the structure maps on points. -/
private theorem base_eq_of_etale_hom {X : Scheme.{u}} {A B : X.Etale} (φ : A ⟶ B) (q : A.left) :
    A.hom.base q = B.hom.base (φ.left.base q) :=
  (congrArg (fun m : A.left ⟶ X => m.base q) (MorphismProperty.Over.w φ)).symm.trans
    (Scheme.Hom.comp_apply φ.left B.hom q)

/-- **An arrow of the affine étale site lies in the image sieve of the second map of Stacks 03RI
at a section of one summand as soon as the orders of vanishing of a unit on the generic fibre
match that section at `x` and vanish away from it.** The two hypotheses are exactly what
`Stacks.EtaleCohomology.closedPointDivisorSheaf.sheafSectionOfDirectSum_eq_ι` asks for, and the
component of the second map at an affine étale `X`-scheme is the family of orders of vanishing by
`Stacks.EtaleCohomology.divisorSequenceSecondMap_hom_app` together with
`Stacks.EtaleCohomology.affineEtaleDivisorApp_apply` and
`Stacks.EtaleCohomology.closedPointDivisorSheafSection_apply`. -/
theorem imageSieve_ι_of_affineEtale {X : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [IsNormal X]
    [IsLocallyNoetherian X] (x : closedPoints X) {U : X.Etale}
    (t : ToType ((closedPointSkyscraper.{u, v} X x).obj.obj (op U)))
    (W : X.AffineEtale) (φ : (Scheme.AffineEtale.Spec X).obj W ⟶ U)
    (a : Additive ((Γ(pullback ((Scheme.AffineEtale.Spec X).obj W).hom
      (genericPointInclusion X), ⊤))ˣ))
    (h0 : ∀ y : closedPoints X, y ≠ x →
      integerSkyscraperDivisorOfPoint.{u, v} ((Scheme.AffineEtale.Spec X).obj W) y.1 a = 0)
    (hx : integerSkyscraperDivisorOfPoint.{u, v} ((Scheme.AffineEtale.Spec X).obj W) x.1 a =
      ((closedPointSkyscraper.{u, v} X x).obj.map φ.op).hom t) :
    Presheaf.imageSieve (divisorSequenceSecondMap.{u, v} X).hom
      ((closedPointDivisorSheaf.ι.{u, v} X x).hom.app (op U) t) φ := by
  refine ⟨ULift.up a, ?_⟩
  have hnat := NatTrans.naturality_apply (closedPointDivisorSheaf.ι.{u, v} X x).hom φ.op t
  have h1 := affineEtaleDivisorApp_apply.{u, v} X W (ULift.up a)
  have h2 := divisorSequenceSecondMap_hom_app.{u, v} X W
  have h3 : (divisorSequenceSecondMap.{u, v} X).hom.app
      (op ((Scheme.AffineEtale.Spec X).obj W)) (ULift.up a) =
      closedPointDivisorSheafSection.{u, v} ((Scheme.AffineEtale.Spec X).obj W) a :=
    (congrArg (fun ψ : ((genericPointDirectImage.{u, v} X).obj
          (Stacks.Kummer.multiplicativeSheaf.{u, v} (Spec X.functionField))).obj.obj
            (op ((Scheme.AffineEtale.Spec X).obj W)) ⟶
          (closedPointDivisorSheaf.{u, v} X).obj.obj
            (op ((Scheme.AffineEtale.Spec X).obj W)) => ψ.hom (ULift.up a)) h2).trans h1
  have h4 := closedPointDivisorSheaf.sheafSectionOfDirectSum_eq_ι.{u, v} X
    ((Scheme.AffineEtale.Spec X).obj W) x
    (closedPointDivisorSections.{u, v} ((Scheme.AffineEtale.Spec X).obj W) a)
    (fun y hy => (closedPointDivisorSections_apply.{u, v} _ a y).trans (h0 y hy))
  rw [← hnat, h3, closedPointDivisorSheafSection_apply, h4]
  exact congrArg (fun z => ((closedPointDivisorSheaf.ι.{u, v} X x).hom.app
      (op ((Scheme.AffineEtale.Spec X).obj W))).hom z)
    ((closedPointDivisorSections_apply.{u, v} _ a x).trans hx)

/-! ### The right-hand exactness of the sequence of Stacks 03RI -/

/-- **A section of a single summand `(i_x)_* 𝐙` over an étale scheme over a smooth curve is étale
locally the divisor of a section of `j_* 𝐆_{m,η}`.** This is the local statement that the
summand-at-a-time reduction
`Stacks.EtaleCohomology.epi_divisorSequenceSecondMapOfCurve_of_forall_imageSieve_ι_mem` of the
right-hand exactness of Stacks 03RI carries as its hypothesis, and it is proved here; see the
implementation notes for the two shrinkings the covering family is built from.

The sieve is covering because it contains, for every point `w` of the étale `X`-scheme, an arrow
whose image contains `w`: that family covers by
`AlgebraicGeometry.Scheme.ofArrows_mem_smallEtaleTopology_iff`. -/
theorem imageSieve_ι_mem_of_isCurve {k : Type u} [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g] (x : closedPoints X) (U : X.Etale)
    (t : ToType ((closedPointSkyscraper.{u, v} X x).obj.obj (op U))) :
    Presheaf.imageSieve (divisorSequenceSecondMapOfCurve.{u, v} g).hom
        ((closedPointDivisorSheaf.ι.{u, v} X x).hom.app (op U) t) ∈
      X.smallEtaleTopology U := by
  have : IsNormal X := isNormal_of_isCurve_of_smooth g
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
  have : Etale U.hom := U.prop
  have hxgen : x.1 ≠ genericPoint X := ne_genericPoint_of_mem_closedPoints_of_isCurve g x
  have key : ∀ w : U.left, ∃ (W : X.AffineEtale)
      (ψ : (Scheme.AffineEtale.Spec X).obj W ⟶ U),
      Presheaf.imageSieve (divisorSequenceSecondMapOfCurve.{u, v} g).hom
          ((closedPointDivisorSheaf.ι.{u, v} X x).hom.app (op U) t) ψ ∧
        w ∈ Set.range ψ.left.base := by
    intro w
    obtain ⟨D, hwD, hD⟩ := exists_opens_eq_of_etale_of_isClosed U.hom x.2 w
    obtain ⟨W₁, φ₁, hint₁, hoi₁, ⟨p₁, hp₁⟩, hrange₁⟩ := exists_affineEtale_isIntegral U D hwD
    have := hint₁
    have := hoi₁
    have hbase₁ := base_eq_of_etale_hom φ₁
    have hsing₁ : ∀ q : ((Scheme.AffineEtale.Spec X).obj W₁).left,
        ((Scheme.AffineEtale.Spec X).obj W₁).hom.base q = x.1 → φ₁.left.base q = w := fun q hq =>
      hD _ (hrange₁ ⟨q, rfl⟩) ((hbase₁ q).symm.trans hq)
    by_cases hwx : U.hom.base w = x.1
    · have hp₁x : ((Scheme.AffineEtale.Spec X).obj W₁).hom.base p₁ = x.1 :=
        (hbase₁ p₁).trans ((congrArg U.hom.base hp₁).trans hwx)
      have : Etale ((Scheme.AffineEtale.Spec X).obj W₁).hom :=
        ((Scheme.AffineEtale.Spec X).obj W₁).prop
      have hco : Order.coheight p₁ = 1 :=
        coheight_eq_one_of_etale_of_isCurve g ((Scheme.AffineEtale.Spec X).obj W₁).hom
          (by rw [hp₁x]; exact hxgen)
      obtain ⟨V, a₀, hp₁V, hord₁, hordz⟩ :=
        exists_etaleGenericFibreOrdOfPoint_eq_and_forall_eq_zero
          ((Scheme.AffineEtale.Spec X).obj W₁) hco 1
      obtain ⟨W₂, φ₂, hint₂, hoi₂, ⟨p₂, hp₂⟩, hrange₂⟩ :=
        exists_affineEtale_isIntegral ((Scheme.AffineEtale.Spec X).obj W₁) V hp₁V
      have := hint₂
      have := hoi₂
      have hbase₂ := base_eq_of_etale_hom φ₂
      have hp₂x : ((Scheme.AffineEtale.Spec X).obj W₂).hom.base p₂ = x.1 :=
        (hbase₂ p₂).trans ((congrArg ((Scheme.AffineEtale.Spec X).obj W₁).hom.base hp₂).trans hp₁x)
      have hfib₂ : ∀ q : ((Scheme.AffineEtale.Spec X).obj W₂).left,
          ((Scheme.AffineEtale.Spec X).obj W₂).hom.base q = x.1 → q = p₂ := fun q hq =>
        (Scheme.Hom.isEmbedding φ₂.left).injective
          (((Scheme.Hom.isEmbedding φ₁.left).injective
            ((hsing₁ _ ((hbase₂ q).symm.trans hq)).trans hp₁.symm)).trans hp₂.symm)
      have hsubsing : Set.Subsingleton
          (((Scheme.AffineEtale.Spec X).obj W₂).hom.base ⁻¹' {x.1}) := fun q hq r hr =>
        (hfib₂ q hq).trans (hfib₂ r hr).symm
      have : Subsingleton ↥((smallEtaleBaseChange (X.fromSpecResidueField x.1)).obj
          ((Scheme.AffineEtale.Spec X).obj W₂)).left :=
        subsingleton_pullback_fromSpecResidueField _ x.1 hsubsing
      have hnonempty : Nonempty ↥((smallEtaleBaseChange (X.fromSpecResidueField x.1)).obj
          ((Scheme.AffineEtale.Spec X).obj W₂)).left :=
        nonempty_pullback_fromSpecResidueField
          ((Scheme.AffineEtale.Spec X).obj W₂).hom hp₂x
      obtain ⟨p₀⟩ := hnonempty
      have hordQ : ∀ z : ((Scheme.AffineEtale.Spec X).obj W₂).left,
          etaleGenericFibreOrdOfPoint ((Scheme.AffineEtale.Spec X).obj W₂) z
              (Additive.ofMul (Units.map (etaleGenericFibreMap φ₂).appTop.hom.toMonoidHom a₀)) =
            etaleGenericFibreOrdOfPoint ((Scheme.AffineEtale.Spec X).obj W₁)
              (φ₂.left.base z) (Additive.ofMul a₀) := fun z =>
        etaleGenericFibreOrdOfPoint_appTop φ₂ z a₀
      refine ⟨W₂, φ₂ ≫ φ₁, imageSieve_ι_of_affineEtale.{u, v} x t W₂ (φ₂ ≫ φ₁)
        (((integerSkyscraperSectionsIsoLocallyConstantMaps.{u, v} X x.1
            ((Scheme.AffineEtale.Spec X).obj W₂)).hom.hom
              (((closedPointSkyscraper.{u, v} X x).obj.map (φ₂ ≫ φ₁).op).hom t) p₀).down •
          Additive.ofMul (Units.map (etaleGenericFibreMap φ₂).appTop.hom.toMonoidHom a₀))
        (fun y hy => ?_) ?_, ⟨p₂, ?_⟩⟩
      · refine integerSkyscraperDivisorOfPoint_eq_zero_of_forall.{u, v} _ y.1 _ (fun p => ?_)
        have hfst := base_pullback_fst_fromSpecResidueField (X := X)
          ((Scheme.AffineEtale.Spec X).obj W₂).hom y.1 p
        have hne : φ₂.left.base ((pullback.fst ((Scheme.AffineEtale.Spec X).obj W₂).hom
            (X.fromSpecResidueField y.1)) p) ≠ p₁ := fun hcontra =>
          hy (Subtype.ext (hfst.symm.trans
            ((hbase₂ _).trans ((congrArg
              ((Scheme.AffineEtale.Spec X).obj W₁).hom.base hcontra).trans hp₁x))))
        rw [map_zsmul, hordQ, hordz _ (hrange₂ ⟨_, rfl⟩) hne, smul_zero]
      · refine integerSkyscraperDivisorOfPoint_eq_of_forall.{u, v} _ x.1 _ _ (fun p => ?_)
        obtain rfl : p = p₀ := Subsingleton.elim p p₀
        have hfst := base_pullback_fst_fromSpecResidueField (X := X)
          ((Scheme.AffineEtale.Spec X).obj W₂).hom x.1 p
        rw [map_zsmul, hfib₂ _ hfst, hordQ, hp₂, hord₁, smul_eq_mul, mul_one]
      · exact (Scheme.Hom.comp_apply φ₂.left φ₁.left p₂).trans
          ((congrArg φ₁.left.base hp₂).trans hp₁)
    · have hempty : IsEmpty ↥(pullback ((Scheme.AffineEtale.Spec X).obj W₁).hom
          (X.fromSpecResidueField x.1)) := by
        refine ⟨fun p => hwx ?_⟩
        have h1 := base_pullback_fst_fromSpecResidueField (X := X)
          ((Scheme.AffineEtale.Spec X).obj W₁).hom x.1 p
        exact (congrArg U.hom.base (hsing₁ _ h1)).symm.trans ((hbase₁ _).symm.trans h1)
      exact ⟨W₁, φ₁, imageSieve_ι_of_affineEtale.{u, v} x t W₁ φ₁ 0 (fun y _ => map_zero _)
        (integerSkyscraperDivisorOfPoint_eq_of_forall.{u, v} _ x.1 0 _ fun p => hempty.elim p),
        ⟨p₁, hp₁⟩⟩
  choose W ψ hS hmem using key
  refine X.smallEtaleTopology.superset_covering ?_
    ((Scheme.ofArrows_mem_smallEtaleTopology_iff ψ).mpr ?_)
  · intro T f hf
    obtain ⟨i, c, rfl⟩ := (Sieve.mem_ofArrows_iff
      (fun i : U.left => (Scheme.AffineEtale.Spec X).obj (W i)) ψ f).mp hf
    exact Sieve.downward_closed _ (hS i) c
  · ext y
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨y, hmem y⟩

/-- **The second map of the fundamental exact sequence of Stacks 03RI is an epimorphism**, for a
smooth curve over a field:
`j_* 𝐆_{m,η} ⟶ ⨁_{x ∈ X_0} (i_x)_* 𝐙 ⟶ 0`
is exact. This is the right-hand exactness of the source, with the algebraically closed base
field of the source weakened to an arbitrary field.

It is
`Stacks.EtaleCohomology.epi_divisorSequenceSecondMapOfCurve_of_forall_imageSieve_ι_mem` with its
hypothesis discharged by `Stacks.EtaleCohomology.imageSieve_ι_mem_of_isCurve`.

Together with the left end,
`Stacks.EtaleCohomology.mono_multiplicativeDirectImageComparison_genericPointInclusion`, and the
vanishing of the composite,
`Stacks.EtaleCohomology.multiplicativeDirectImageComparison_comp_divisorSequenceSecondMapOfCurve`,
what remains of Stacks 03RI is the exactness in the middle,
`Stacks.EtaleCohomology.exact_divisorSequenceOfCurve`; the four together are the short exactness
of the sequence, `Stacks.EtaleCohomology.shortExact_divisorSequenceOfCurve`, which is what
discharges the short exactness hypothesis of
`Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_smoothCurve`. -/
@[stacks 03RI "the right-hand exactness of the sequence for a smooth curve over a field: the
second map, as constructed here, is an epimorphism of étale sheaves; the exactness in the middle
is proved separately, as Stacks.EtaleCohomology.exact_divisorSequenceOfCurve"]
theorem epi_divisorSequenceSecondMapOfCurve {k : Type u} [Field k] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g] :
    Epi (divisorSequenceSecondMapOfCurve.{u, v} g) :=
  have : IsNormal X := isNormal_of_isCurve_of_smooth g
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isCurve g
  epi_divisorSequenceSecondMapOfCurve_of_forall_imageSieve_ι_mem.{u, v} g
    (imageSieve_ι_mem_of_isCurve.{u, v} g)

end Stacks.EtaleCohomology

end
