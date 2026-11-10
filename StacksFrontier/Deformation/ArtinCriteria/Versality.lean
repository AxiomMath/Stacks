module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.Versality
import StacksCore.Tactic.StacksAttribute

/-!
# Smoothness at a point and versality

For schemes locally of finite type over a locally Noetherian base, a morphism `f : U ⟶ V` of
schemes over `S` is smooth at a finite-type point `u₀` of `U` exactly when the corresponding
object of the category of schemes over `V`, fibred over the schemes over `S`, is versal at
`u₀`.

The proof is the one in the source. Versality at `u₀` is the lifting property for surjections
of Artinian local algebras with residue field the residue field of `u₀`; the infinitesimal
lifting criterion for smoothness is the same property for all surjections with nilpotent
kernel. The kernel of a surjection out of an Artinian local ring is nilpotent, which gives one
direction, and an arbitrary nilpotent surjection is reduced to the Artinian local case by
passing to the local ring at the image point and to the quotients by the powers of the kernel.

## Main results

* `Deformation.Artin.smoothAt_iff_isVersalAt`: smoothness at a finite-type point is equivalent
  to versality of the corresponding object.

## Implementation notes

The category of schemes over `V`, fibred over the schemes over `S`, is presented as the slice
of `Over S` at `V`, so that the object associated with `f` and the forgetful functor to
`Over S` are both explicit. The fppf topology changes neither the underlying fibred category
nor the pointwise versality predicate, so no site enters the statement.

Throughout, points of `Spec R` are written as primes of `R` — `IsLocalRing.closedPoint R` for
the closed point, say. That identification is definitional but passes through semireducible
definitions, so the terms it produces are not type-correct at the transparency used by rewrite
matching and by instance synthesis; the file therefore makes that chain of definitions locally
reducible, and states the auxiliary `specializes_comp_fromSpecStalk` for an abstract scheme so
that the composites of its conclusion sit on a single instance path.

## References

* [Stacks Project, Tag 0CXL](https://stacks.math.columbia.edu/tag/0CXL)
* [Stacks Project, Tag 02HX](https://stacks.math.columbia.edu/tag/02HX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

/-
The points of `Spec R` are the primes of `R`, but the chain of definitions realizing that
(`Spec`, `Spec.locallyRingedSpaceObj`, `Spec.sheafedSpaceObj`, `Spec.topObj`) is semireducible,
so a term such as `IsLocalRing.closedPoint R : Spec R` is accepted by the elaborator at default
transparency and is then not type-correct at the `implicit` transparency used by rewrite matching
and by instance synthesis.  Making the chain reducible is what lets `rw`, `simp only` and
`infer_instance` see through it; see also the use of `Opens.mem_top` instead of `trivial` below,
which is the same issue for `x ∈ (⊤ : Opens _)`.
-/
attribute [local implicit_reducible] AlgebraicGeometry.Spec
  AlgebraicGeometry.Spec.locallyRingedSpaceObj AlgebraicGeometry.Spec.sheafedSpaceObj
  AlgebraicGeometry.Spec.topObj

namespace Deformation.Artin

universe u

private theorem ker_nilpotent_of_artinian_surjective
    {R T : Type u} [CommRing R] [CommRing T] [IsArtinianRing R]
    [IsLocalRing R] [IsLocalRing T] (φ : R →+* T)
    (_hsurj : Function.Surjective φ) : IsNilpotent (RingHom.ker φ) := by
  have hker : RingHom.ker φ ≠ ⊤ := RingHom.ker_ne_top φ
  have hle : RingHom.ker φ ≤ Ideal.jacobson (⊥ : Ideal R) := by
    rw [Ideal.jacobson_bot, IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact IsLocalRing.le_maximalIdeal hker
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  exact ⟨n, le_bot_iff.mp ((Ideal.pow_right_mono hle n).trans_eq hn)⟩

/-! Precomposing with a specialization map moves the base point of `fromSpecStalk`.

Stated for an abstract scheme and an abstract ring map so that the two `≫`s of the conclusion
sit on the same instance path; at the use sites the morphisms carry types that are only
definitionally of this shape, and `exact` unifies them where `rw` cannot. -/
private theorem specializes_comp_fromSpecStalk {X : Scheme.{u}} {x y : X} (h : x ⤳ y)
    {R : CommRingCat.{u}} (ψ : X.presheaf.stalk x ⟶ R) :
    Spec.map (X.presheaf.stalkSpecializes h ≫ ψ) ≫ X.fromSpecStalk y =
      Spec.map ψ ≫ X.fromSpecStalk x := by
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

/-- Evaluating `Spec.map φ ≫ γ` at the closed point of `Spec B` for a local `φ : B' ⟶ B`
evaluates `γ` at the closed point of `Spec B'`. -/
private theorem specMap_comp_base_closedPoint {X : Scheme.{u}} {B' B : CommRingCat.{u}}
    [IsLocalRing B] [IsLocalRing B'] (φ : B' ⟶ B) [IsLocalHom φ.hom] (γ : Spec B' ⟶ X) :
    (Spec.map φ ≫ γ).base (IsLocalRing.closedPoint B) = γ.base (IsLocalRing.closedPoint B') := by
  rw [Scheme.Hom.comp_base, TopCat.comp_app, AlgebraicGeometry.Spec_closedPoint (f := φ)]

/-- The residue map of an object of `𝒞_Λ` is a local homomorphism. -/
private theorem isLocalHom_residueMap {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    IsLocalHom (Deformation.Artin.residueMap A) :=
  Function.Surjective.isLocalHom _ <| A.residueEquiv.toRingEquiv.surjective.comp
    (IsLocalRing.residue_surjective (R := A))

private theorem formallySmooth_liftsAgainstSurjective
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (hfs : letI : Algebra (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
        (f.stalkMap x).hom.toAlgebra
      Algebra.FormallySmooth (S.presheaf.stalk (f.base x)) (X.presheaf.stalk x))
    {B' B : CommRingCat.{u}} (φ : B' ⟶ B)
    [IsLocalRing B] [IsLocalRing B'] (hsurj : Function.Surjective φ.hom)
    (hker : IsNilpotent (RingHom.ker φ.hom))
    (α : Spec B ⟶ X) (β : Spec B' ⟶ S)
    (hcomm : α ≫ f = Spec.map φ ≫ β)
    (hclosed : α.base (IsLocalRing.closedPoint B) = x) :
    ∃ γ : Spec B' ⟶ X, Spec.map φ ≫ γ = α ∧ γ ≫ f = β := by
  have hφloc : IsLocalHom φ.hom := Function.Surjective.isLocalHom φ.hom hsurj
  subst hclosed
  have hpt : β.base (IsLocalRing.closedPoint B') = f.base (α.base (IsLocalRing.closedPoint B)) :=
    (specMap_comp_base_closedPoint φ β).symm.trans
      (congrArg (fun g => g.base (IsLocalRing.closedPoint B)) hcomm.symm)
  let a : X.presheaf.stalk (α.base (IsLocalRing.closedPoint B)) ⟶ B :=
    Scheme.stalkClosedPointTo α
  let b : S.presheaf.stalk (f.base (α.base (IsLocalRing.closedPoint B))) ⟶ B' :=
    S.presheaf.stalkSpecializes (Specializes.of_eq hpt) ≫ Scheme.stalkClosedPointTo β
  have hcompat : f.stalkMap (α.base (IsLocalRing.closedPoint B)) ≫ a = b ≫ φ :=
    InfinitesimalLifting.stalkMap_stalkClosedPointTo_comm f φ α β hcomm hpt
  let : Algebra (S.presheaf.stalk (f.base (α.base (IsLocalRing.closedPoint B))))
      (X.presheaf.stalk (α.base (IsLocalRing.closedPoint B))) :=
    (f.stalkMap (α.base (IsLocalRing.closedPoint B))).hom.toAlgebra
  let : Algebra (S.presheaf.stalk (f.base (α.base (IsLocalRing.closedPoint B)))) B' :=
    b.hom.toAlgebra
  let : Algebra (S.presheaf.stalk (f.base (α.base (IsLocalRing.closedPoint B)))) B :=
    (b ≫ φ).hom.toAlgebra
  have hfs' : Algebra.FormallySmooth
      (S.presheaf.stalk (f.base (α.base (IsLocalRing.closedPoint B))))
      (X.presheaf.stalk (α.base (IsLocalRing.closedPoint B))) := hfs
  let aA : (X.presheaf.stalk (α.base (IsLocalRing.closedPoint B))) →ₐ[
      S.presheaf.stalk (f.base (α.base (IsLocalRing.closedPoint B)))] B :=
    { a.hom with
      commutes' := fun r => by
        change a.hom ((f.stalkMap (α.base (IsLocalRing.closedPoint B))).hom r) = (b ≫ φ).hom r
        simpa using congrArg (fun (g : _ ⟶ B) => g.hom r) hcompat }
  let φA : B' →ₐ[S.presheaf.stalk (f.base (α.base (IsLocalRing.closedPoint B)))] B :=
    { φ.hom with
      commutes' := fun r => by
        change φ.hom (b.hom r) = (b ≫ φ).hom r
        simp only [CommRingCat.hom_comp, RingHom.coe_comp]
        rfl }
  let c := hfs'.liftOfSurjective aA φA hsurj hker
  have hc : φA.comp c = aA := hfs'.comp_liftOfSurjective aA φA hsurj hker
  let cR := CommRingCat.ofHom c.toRingHom
  have hcφ : cR ≫ φ = a := by
    apply CommRingCat.hom_ext
    ext y
    exact congrArg (fun (g : _ →ₐ[S.presheaf.stalk (f.base (α.base
      (IsLocalRing.closedPoint B)))] B) => g y) hc
  have hbc : f.stalkMap (α.base (IsLocalRing.closedPoint B)) ≫ cR = b := by
    apply CommRingCat.hom_ext
    ext r
    have h := c.commutes r
    rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra] at h
    exact h
  refine ⟨Spec.map cR ≫ X.fromSpecStalk (α.base (IsLocalRing.closedPoint B)), ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp, hcφ]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk α
  · rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk f,
      ← Spec.map_comp_assoc, hbc]
    exact (specializes_comp_fromSpecStalk _ _).trans
      (Scheme.Spec_stalkClosedPointTo_fromSpecStalk β)

private theorem stalkClosedPointTo_fromSpecResidueField
    (X : Scheme.{u}) (x : X) :
    Scheme.stalkClosedPointTo (X.fromSpecResidueField x) =
      X.residue ((X.fromSpecResidueField x) (IsLocalRing.closedPoint (X.residueField x))) ≫
        (X.residueFieldCongr (Scheme.fromSpecResidueField_apply x
          (IsLocalRing.closedPoint (X.residueField x)))).hom := by
  let τ := X.fromSpecResidueField x
  let p := τ (IsLocalRing.closedPoint (X.residueField x))
  have hp : p = x := Scheme.fromSpecResidueField_apply x _
  let : IsLocalHom (Scheme.stalkClosedPointTo τ).hom :=
    @Scheme.isLocalHom_stalkClosedPointTo' X (↑(X.residueField x)) inferInstance
      inferInstance τ
  let e := X.residueFieldCongr hp
  let d : X.residueField p ⟶ X.residueField x :=
    @Scheme.descResidueField (↑(X.residueField x)) inferInstance X p
      (Scheme.stalkClosedPointTo τ) (Scheme.isLocalHom_stalkClosedPointTo' τ)
  have he : Spec.map e.hom ≫ X.fromSpecResidueField p = X.fromSpecResidueField x :=
    by simp [e, p]
  have hde : d = e.hom := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecResidueField p)).mp
    calc
      Spec.map d ≫ X.fromSpecResidueField p = τ :=
        Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField
          (X.residueField x) X τ
      _ = X.fromSpecResidueField x := rfl
      _ = Spec.map e.hom ≫ X.fromSpecResidueField p := he.symm
  calc
    Scheme.stalkClosedPointTo (X.fromSpecResidueField x) =
        X.residue p ≫ d := by
          have h := @Scheme.residue_descResidueField (↑(X.residueField x)) inferInstance
            X p (Scheme.stalkClosedPointTo τ)
            (Scheme.isLocalHom_stalkClosedPointTo' τ)
          simpa [d, τ, p] using h.symm
    _ = X.residue p ≫ e.hom := by rw [hde]
    _ = _ := rfl

/-- Smoothness at a finite-type point is equivalent to versality of the
corresponding object of the slice fibred over schemes over `S`. -/
@[stacks 0CXL]
public theorem smoothAt_iff_isVersalAt
    {U V S : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType (f ≫ g)]
    [LocallyOfFiniteType g] (u₀ : U)
    (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀) :
    InfinitesimalLifting.SmoothAt f u₀ ↔
      Deformation.Artin.IsVersalAt (Over.mk (f ≫ g))
        (Over.forget (Over.mk g)) u₀
        (Over.mk (Over.homMk f (by simp))) rfl := by
  constructor
  · intro h A B φ hsurj y z hy hz i hi a ha
    let s := Deformation.Artin.basePoint (Over.mk (f ≫ g)) u₀
    let R := S.presheaf.stalk s
    let k := U.residueField u₀
    let : Algebra (S.presheaf.stalk (Deformation.Artin.basePoint (Over.mk (f ≫ g)) u₀))
        ((Over.mk (f ≫ g)).left.residueField u₀) :=
      Deformation.Artin.residueFieldAlgebra (Over.mk (f ≫ g)) u₀
    rcases y with ⟨yS, yR, yHom⟩
    rcases z with ⟨zS, zR, zHom⟩
    cases hy
    cases hz
    let Φ : CommRingCat.of B ⟶ CommRingCat.of A :=
      CommRingCat.ofHom φ.hom.toRingHom
    let α : Spec (CommRingCat.of A) ⟶ (Over.mk (f ≫ g)).left := a.left.left
    let β : Spec (CommRingCat.of B) ⟶ V := zHom.left
    have hi' : i.left.left = Spec.map Φ := by
      simpa [Over.forget_map, Φ] using hi
    have ha' : Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap A)) ≫ α =
        (Over.mk (f ≫ g)).left.fromSpecResidueField u₀ := by
      simpa [Over.forget_map] using ha
    have hclosed : α.base (IsLocalRing.closedPoint A) = u₀ := by
      have := isLocalHom_residueMap A
      have hp := congrArg (fun q : Spec (CommRingCat.of
          ((Over.mk (f ≫ g)).left.residueField u₀)) ⟶ (Over.mk (f ≫ g)).left =>
        q (IsLocalRing.closedPoint ((Over.mk (f ≫ g)).left.residueField u₀))) ha'
      rw [specMap_comp_base_closedPoint (CommRingCat.ofHom (Deformation.Artin.residueMap A))] at hp
      have hright := Scheme.fromSpecResidueField_apply (X := U) u₀
        (IsLocalRing.closedPoint (U.residueField u₀))
      exact hp.trans hright
    have hcat : i.left ≫ zHom = a.left ≫ (Over.mk (Over.homMk f (by simp))).hom :=
      i.w.trans a.w.symm
    have hcat' : i.left.left ≫ β = α ≫ f := by
      simpa [α, β] using congrArg Over.Hom.left hcat
    have hcomm : α ≫ f = Spec.map Φ ≫ β := by
      rw [← hi']
      exact hcat'.symm
    have hsurj' : Function.Surjective Φ.hom := by
      change Function.Surjective φ.hom.toRingHom
      exact hsurj
    have hker : IsNilpotent (RingHom.ker Φ.hom) :=
      ker_nilpotent_of_artinian_surjective φ.hom.toRingHom hsurj'
    obtain ⟨γ, hγ₁, hγ₂⟩ := formallySmooth_liftsAgainstSurjective f u₀
      (h.formallySmooth_stalkMap f u₀) Φ hsurj' hker α β hcomm hclosed
    let baseB : Over S := Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap
        (S.presheaf.stalk (Deformation.Artin.basePoint (Over.mk (f ≫ g)) u₀)) B)) ≫
        S.fromSpecStalk (Deformation.Artin.basePoint (Over.mk (f ≫ g)) u₀))
    have hzHom : β ≫ g = baseB.hom := by
      simpa [β, baseB] using zHom.w
    have hγS : γ ≫ (f ≫ g) = baseB.hom := by
      rw [← Category.assoc, hγ₂]
      exact hzHom
    let fOver : Over.mk (f ≫ g) ⟶ Over.mk g := Over.homMk f (by simp)
    let b₀ : baseB ⟶ Over.mk (f ≫ g) := Over.homMk γ hγS
    have hb₀ : b₀ ≫ fOver = zHom := CostructuredArrow.hom_ext _ _ hγ₂
    refine ⟨Over.homMk b₀ hb₀, ?_⟩
    apply CostructuredArrow.hom_ext
    apply CostructuredArrow.hom_ext
    change i.left.left ≫ γ = a.left.left
    rw [hi']
    simpa [α] using hγ₁
  · intro h
    let Uover : Over S := Over.mk g
    let q : Over Uover ⥤ Over S := Over.forget Uover
    let x₀ : Over Uover := Over.mk
      (Over.homMk (U := Over.mk (f ≫ g)) (V := Uover) f (by simp [Uover]))
    let s := Deformation.Artin.basePoint (Over.mk (f ≫ g)) u₀
    let R := S.presheaf.stalk s
    let K := U.residueField u₀
    let : Algebra R K := Deformation.Artin.residueFieldAlgebra (Over.mk (f ≫ g)) u₀
    have hres : InfinitesimalLifting.LiftsAgainstResiduallyTrivialSmallExtension f u₀ := by
      intro B' B Φ hsmall _ α β hcomm hclosed hresIso
      rcases hsmall with ⟨hB', hB, hArtB', hArtB, hsurj, hlen⟩
      let : IsLocalRing B' := hB'
      let : IsArtinianRing B := hArtB
      let : IsArtinianRing B' := hArtB'
      subst u₀
      have hΦloc : IsLocalHom Φ.hom :=
        Function.Surjective.isLocalHom Φ.hom hsurj
      let : IsLocalHom Φ.hom := hΦloc
      let cp : Spec (CommRingCat.of B) := IsLocalRing.closedPoint B
      let cp' : Spec (CommRingCat.of B') := IsLocalRing.closedPoint B'
      have hpt : β.base cp' = f.base (α.base cp) :=
        (specMap_comp_base_closedPoint Φ β).symm.trans (congrArg (fun q => q.base cp) hcomm.symm)
      have hptS : (β ≫ g).base cp' = (f ≫ g).base (α.base cp) := by
        simpa using congrArg g.base hpt
      let θ : U ⟶ S := f ≫ g
      have hptS' : g.base (β.base cp') = θ.base (α.base cp) := by
        simpa [θ] using hptS
      have hs : Deformation.Artin.basePoint (Over.mk (f ≫ g))
          (α.base (IsLocalRing.closedPoint B)) =
          θ.base (α.base (IsLocalRing.closedPoint B)) := by
        dsimp [Deformation.Artin.basePoint, Deformation.Artin.residueFieldBasePoint, θ]
        simp [Scheme.fromSpecResidueField_apply]
      let σ : CommRingCat.of R ⟶
          CommRingCat.of (S.presheaf.stalk (θ.base (α.base cp))) :=
        S.presheaf.stalkSpecializes (Specializes.of_eq hs.symm)
      let bθ : CommRingCat.of (S.presheaf.stalk (θ.base (α.base cp))) ⟶
          CommRingCat.of B' :=
        S.presheaf.stalkSpecializes (Specializes.of_eq hptS') ≫
          Scheme.stalkClosedPointTo (β ≫ g)
      let b := σ ≫ bθ
      let bThin := b ≫ Φ
      have hcommS : α ≫ θ = Spec.map Φ ≫ (β ≫ g) := by
        calc
          α ≫ θ = (α ≫ f) ≫ g := by simp [θ, Category.assoc]
          _ = (Spec.map Φ ≫ β) ≫ g := by rw [hcomm]
          _ = Spec.map Φ ≫ (β ≫ g) := by simp [Category.assoc]
      have hcompat := InfinitesimalLifting.stalkMap_stalkClosedPointTo_comm θ Φ α (β ≫ g)
        hcommS hptS
      let : Algebra R B' := b.hom.toAlgebra
      let : Algebra R B := bThin.hom.toAlgebra
      let a : CommRingCat.of (U.presheaf.stalk (α.base cp)) ⟶ CommRingCat.of B :=
        Scheme.stalkClosedPointTo α
      have harel : a = Scheme.Hom.stalkMap α cp ≫ (stalkClosedPointIso B).hom :=
        CommRingCat.hom_ext rfl
      let : IsLocalHom a.hom := by
        rw [harel]
        infer_instance
      let a0 : CommRingCat.of R ⟶ CommRingCat.of (U.presheaf.stalk (α.base cp)) :=
        σ ≫ θ.stalkMap (α.base cp)
      let : Algebra R (U.presheaf.stalk (α.base cp)) := a0.hom.toAlgebra
      let : Algebra (U.presheaf.stalk (α.base cp)) K :=
        (IsLocalRing.residue (U.presheaf.stalk (α.base cp))).toAlgebra
      have hAK : algebraMap R K =
          (algebraMap (U.presheaf.stalk (α.base cp)) K).comp a0.hom := by
        let τ := U.fromSpecResidueField (α.base cp)
        have hτ : τ (IsLocalRing.closedPoint K) = α.base cp := by
          simp [τ]
        let hp : α.base cp ⤳ τ (IsLocalRing.closedPoint K) :=
          Specializes.of_eq hτ.symm
        have hσ : σ = S.presheaf.stalkSpecializes
            (Specializes.of_eq (congrArg θ hτ.symm)) := rfl
        have hres : U.presheaf.stalkSpecializes hp ≫ U.residue (α.base cp) =
            Scheme.stalkClosedPointTo τ := by
          rw [stalkClosedPointTo_fromSpecResidueField]
          simpa [hp] using (Scheme.residue_residueFieldCongr U hτ).symm
        change (Scheme.stalkClosedPointTo
          (τ ≫ θ)).hom =
          (algebraMap (U.presheaf.stalk (α.base cp)) K).comp a0.hom
        rw [Scheme.stalkClosedPointTo_comp]
        change (θ.stalkMap (τ (IsLocalRing.closedPoint K)) ≫
          Scheme.stalkClosedPointTo τ).hom =
          (U.residue (α.base cp)).hom.comp
            ((σ ≫ θ.stalkMap (α.base cp)).hom)
        have hassoc := Scheme.Hom.stalkSpecializes_stalkMap_assoc θ
          (α.base cp) (τ (IsLocalRing.closedPoint K)) hp (U.residue (α.base cp))
        have hcat : θ.stalkMap (τ (IsLocalRing.closedPoint K)) ≫
            Scheme.stalkClosedPointTo τ =
          σ ≫ θ.stalkMap (α.base cp) ≫ U.residue (α.base cp) := by
          rw [← hres, hσ]
          exact hassoc.symm
        have hcat' := congrArg CommRingCat.Hom.hom
          (hcat.trans (Category.assoc σ (θ.stalkMap (α.base cp)) (U.residue (α.base cp))).symm)
        simp only [CommRingCat.hom_comp] at hcat'
        exact hcat'
      let : IsScalarTower R (U.presheaf.stalk (α.base cp)) K :=
        IsScalarTower.of_algebraMap_eq' hAK
      have hacompat : a0 ≫ a = bThin := by
        change (σ ≫ θ.stalkMap (α.base cp)) ≫ a = (σ ≫ bθ) ≫ Φ
        calc
          _ = σ ≫ (θ.stalkMap (α.base cp) ≫ a) := Category.assoc _ _ _
          _ = σ ≫ ((S.presheaf.stalkSpecializes
                (Specializes.of_eq hptS) ≫ Scheme.stalkClosedPointTo (β ≫ g)) ≫ Φ) := by
            rw [hcompat]
          _ = (σ ≫ bθ) ≫ Φ := (Category.assoc _ _ _).symm
      let aAlg : (U.presheaf.stalk (α.base cp)) →ₐ[
          R] B :=
        { a.hom with
          commutes' := fun r => by
            change a.hom (a0.hom r) = bThin.hom r
            exact congrArg (fun z : _ ⟶ CommRingCat.of B => z.hom r) hacompat }
      let : IsLocalHom aAlg.toRingHom := by
        change IsLocalHom a.hom
        rw [harel]
        infer_instance
      let : IsLocalHom aAlg :=
        ⟨fun x hx => (inferInstance : IsLocalHom aAlg.toRingHom).map_nonunit x hx⟩
      let eInduced := IsLocalRing.ResidueField.mapAlgHom aAlg
      let eB_ring : K ≃+* IsLocalRing.ResidueField B := by
        apply RingEquiv.ofBijective eInduced.toRingHom
        let eSpec : (Spec B).residueField cp ≃+* IsLocalRing.ResidueField B :=
          IsLocalRing.ResidueField.mapEquiv
            (stalkClosedPointIso B).commRingCatIsoToRingEquiv
        have hmap : eInduced.toRingHom =
            eSpec.toRingHom.comp (α.residueFieldMap cp).hom := by
          ext z
          dsimp [eInduced, IsLocalRing.ResidueField.mapAlgHom,
            Scheme.Hom.residueFieldMap]
          change IsLocalRing.ResidueField.map
              ((stalkClosedPointIso B).hom.hom.comp (α.stalkMap cp).hom) z =
            eSpec (IsLocalRing.ResidueField.map (α.stalkMap cp).hom z)
          change IsLocalRing.ResidueField.map
              ((stalkClosedPointIso B).hom.hom.comp (α.stalkMap cp).hom) z =
            IsLocalRing.ResidueField.map (stalkClosedPointIso B).hom.hom
              (IsLocalRing.ResidueField.map (α.stalkMap cp).hom z)
          exact (IsLocalRing.ResidueField.map_map (α.stalkMap cp).hom
            (stalkClosedPointIso B).hom.hom z).symm
        rw [hmap]
        have hαbij : Function.Bijective (α.residueFieldMap cp).hom :=
          (ConcreteCategory.isIso_iff_bijective _).mp hresIso
        exact eSpec.bijective.comp hαbij
      let eB : K ≃ₐ[R] IsLocalRing.ResidueField B :=
        AlgEquiv.ofRingEquiv (f := eB_ring) (by
          intro r
          rw [hAK]
          change eB_ring (IsLocalRing.residue (U.presheaf.stalk (α.base cp))
              (a0.hom r)) =
            IsLocalRing.residue B (bThin.hom r)
          change IsLocalRing.ResidueField.mapAlgHom aAlg
              (IsLocalRing.residue (U.presheaf.stalk (α.base cp)) (a0.hom r)) = _
          rw [IsLocalRing.ResidueField.mapAlgHom_residue]
          congr 1
          exact (congrArg (fun z : _ ⟶ CommRingCat.of B => z.hom r) hacompat))
      let φAlg : B' →ₐ[R] B :=
        { Φ.hom with
          commutes' := fun r => by
            change Φ.hom (b.hom r) = bThin.hom r
            simp [bThin, CommRingCat.hom_comp, RingHom.coe_comp] }
      let : IsLocalHom φAlg.toRingHom := by
        change IsLocalHom Φ.hom
        exact hΦloc
      let : IsLocalHom φAlg :=
        ⟨fun x hx => hΦloc.map_nonunit x hx⟩
      let eφMap := IsLocalRing.ResidueField.mapAlgHom φAlg
      have hφsurj : Function.Surjective eφMap.toRingHom := by
        intro y
        obtain ⟨b₀, rfl⟩ := IsLocalRing.residue_surjective y
        obtain ⟨b₁, rfl⟩ := hsurj b₀
        exact ⟨IsLocalRing.residue B' b₁, by
          simp [eφMap, IsLocalRing.ResidueField.mapAlgHom, φAlg]⟩
      have hφinj : Function.Injective eφMap.toRingHom := RingHom.injective eφMap.toRingHom
      let eφ : IsLocalRing.ResidueField B' ≃ₐ[
          R] IsLocalRing.ResidueField B :=
        AlgEquiv.ofBijective eφMap ⟨hφinj, hφsurj⟩
      let eBThick := eB.trans eφ.symm
      let Aobj : Deformation.ArtinianLocalAlgCat.{u, u, u}
          R K :=
        { carrier := B
          residueEquiv := eB.symm }
      let Bobj : Deformation.ArtinianLocalAlgCat.{u, u, u}
          R K :=
        { carrier := B'
          residueEquiv := eBThick.symm }
      let φobj : Bobj ⟶ Aobj :=
        { hom := φAlg
          isLocal := hΦloc
          residue_comm := by
            intro z
            apply eB.injective
            dsimp [Aobj, Bobj]
            rfl }
      let baseThin : Over S := Over.mk
        (Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ S.fromSpecStalk s)
      let baseThick : Over S := Over.mk
        (Spec.map (CommRingCat.ofHom (algebraMap R B')) ≫ S.fromSpecStalk s)
      have hβbase : β ≫ g = baseThick.hom := by
        symm
        change Spec.map b ≫ S.fromSpecStalk s = β ≫ g
        exact (specializes_comp_fromSpecStalk (Specializes.of_eq hs.symm) bθ).trans
          ((specializes_comp_fromSpecStalk (Specializes.of_eq hptS')
              (Scheme.stalkClosedPointTo (β ≫ g))).trans
            (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (β ≫ g)))
      have hαbase : α ≫ θ = baseThin.hom := by
        calc
          α ≫ θ = Spec.map Φ ≫ (β ≫ g) := hcommS
          _ = Spec.map Φ ≫ baseThick.hom := by rw [hβbase]
          _ = Spec.map Φ ≫ Spec.map b ≫ S.fromSpecStalk s := (Category.assoc _ _ _).symm
          _ = Spec.map (b ≫ Φ) ≫ S.fromSpecStalk s := by
            rw [← Category.assoc, ← Spec.map_comp]
          _ = baseThin.hom := by
            dsimp [baseThin]
            congr 1
      let yHom : baseThin ⟶ Uover := Over.homMk (α ≫ f) hαbase
      let zHom : baseThick ⟶ Uover := Over.homMk β hβbase
      let y : Over Uover := Over.mk yHom
      let z : Over Uover := Over.mk zHom
      have hy : q.obj y = baseThin := rfl
      have hz : q.obj z = baseThick := rfl
      have hbasei : Spec.map Φ ≫ baseThick.hom = baseThin.hom := by
        calc
          Spec.map Φ ≫ baseThick.hom = Spec.map Φ ≫ (β ≫ g) := by rw [hβbase]
          _ = α ≫ θ := hcommS.symm
          _ = baseThin.hom := hαbase
      let i₀ : baseThin ⟶ baseThick := Over.homMk (Spec.map Φ) hbasei
      have houteri : i₀ ≫ zHom = yHom := CostructuredArrow.hom_ext _ _ hcomm.symm
      let i : y ⟶ z := Over.homMk i₀ houteri
      have hi :
          eqToHom (congrArg Over.left hy).symm ≫ (q.map i).left ≫
            eqToHom (congrArg Over.left hz) =
          Spec.map (CommRingCat.ofHom φobj.hom.toRingHom) := by
        rfl
      let xObj : Over Uover := x₀
      let a₀ : baseThin ⟶ Over.mk (f ≫ g) := Over.homMk α hαbase
      have houtera : a₀ ≫ x₀.hom = yHom := by
        apply CostructuredArrow.hom_ext
        rfl
      let a : y ⟶ xObj := Over.homMk a₀ houtera
      have ha :
          Spec.map (CommRingCat.ofHom (Deformation.Artin.residueMap Aobj)) ≫
            eqToHom (congrArg Over.left hy).symm ≫ (q.map a).left ≫
            eqToHom (congrArg Over.left rfl) = U.fromSpecResidueField (α.base cp) := by
        let ρ : CommRingCat.of B ⟶ CommRingCat.of K :=
          CommRingCat.ofHom (Deformation.Artin.residueMap Aobj)
        let : IsLocalHom ρ.hom := isLocalHom_residueMap Aobj
        have hρa : Scheme.stalkClosedPointTo α ≫ ρ = U.residue (α.base cp) := by
          apply CommRingCat.hom_ext
          ext r
          change eB.symm (IsLocalRing.residue B
            ((Scheme.stalkClosedPointTo α).hom r)) = U.residue (α.base cp) r
          have hm := IsLocalRing.ResidueField.mapAlgHom_residue aAlg r
          change eB.symm (IsLocalRing.residue B (aAlg r)) = _
          rw [← hm]
          change eB.symm (eB (U.residue (α.base cp) r)) = _
          exact eB.symm_apply_apply _
        let pB := (Spec.map ρ).base (IsLocalRing.closedPoint K)
        have hpB : pB = cp := AlgebraicGeometry.Spec_closedPoint (f := ρ)
        let xρ := (Spec.map ρ ≫ α).base (IsLocalRing.closedPoint K)
        have hpoint : (Spec.map ρ ≫ α).base (IsLocalRing.closedPoint K) = α.base cp := by
          change α.base pB = α.base cp
          rw [hpB]
        let hpInsep : Inseparable xρ (α.base cp) := Inseparable.of_eq hpoint
        have hlocal : (U.presheaf.stalkCongr hpInsep).hom ≫
            (Scheme.stalkClosedPointTo α ≫ ρ) =
            Scheme.stalkClosedPointTo (Spec.map ρ ≫ α) := by
          rw [Scheme.stalkClosedPointTo_comp, InfinitesimalLifting.stalkClosedPointTo_specMap ρ]
          rw [TopCat.Presheaf.stalkCongr_hom]
          have hnat := Scheme.Hom.stalkSpecializes_stalkMap α cp pB
            (Specializes.of_eq hpB.symm)
          have hnat' := congrArg
            (fun m => m ≫ (stalkClosedPointIso B).hom ≫ ρ) hnat
          convert hnat' using 1
          rfl
        have hresf : Scheme.stalkClosedPointTo (Spec.map ρ ≫ α) =
            U.residue xρ ≫ (U.residueFieldCongr hpoint).hom := by
          rw [← hlocal, hρa, Scheme.residue_residueFieldCongr]
        let : IsLocalHom (Scheme.stalkClosedPointTo (Spec.map ρ ≫ α)).hom :=
          Scheme.isLocalHom_stalkClosedPointTo' (Spec.map ρ ≫ α)
        have hdesc : U.descResidueField
            (Scheme.stalkClosedPointTo (Spec.map ρ ≫ α)) =
              (U.residueFieldCongr hpoint).hom := by
          apply (cancel_epi (U.residue xρ)).mp
          rw [Scheme.residue_descResidueField, hresf]
        let τ : Spec (CommRingCat.of K) ⟶ U := U.fromSpecResidueField (α.base cp)
        let : IsLocalHom (Scheme.stalkClosedPointTo τ).hom :=
          Scheme.isLocalHom_stalkClosedPointTo' τ
        let hpCanon := Scheme.fromSpecResidueField_apply (X := U) (α.base cp)
          (IsLocalRing.closedPoint K)
        let pCanon := τ (IsLocalRing.closedPoint K)
        have hdescCanonical : U.descResidueField
            (Scheme.stalkClosedPointTo τ) = (U.residueFieldCongr hpCanon).hom := by
          apply (cancel_epi (U.residue pCanon)).mp
          rw [Scheme.residue_descResidueField,
            stalkClosedPointTo_fromSpecResidueField]
        have hcanonical :
            Spec.map ρ ≫ α =
              U.fromSpecResidueField (α.base cp) := by
          apply (Scheme.SpecToEquivOfField (↑K) U).injective
          rw [Scheme.SpecToEquivOfField_eq_iff]
          refine ⟨?_, ?_⟩
          · rw [Scheme.SpecToEquivOfField_apply_fst,
              Scheme.SpecToEquivOfField_apply_fst]
            exact hpoint.trans hpCanon.symm
          rw [Scheme.SpecToEquivOfField_apply_snd,
            Scheme.SpecToEquivOfField_apply_snd, hdesc, hdescCanonical]
          exact (Scheme.residueFieldCongr_trans_hom U _ hpCanon).symm
        simpa [q, a, a₀, y, hy, x₀, Uover] using hcanonical
      obtain ⟨lift, hlift⟩ := h Aobj Bobj φobj hsurj y z hy hz i hi a ha
      let γ : Spec (CommRingCat.of B') ⟶ U := lift.left.left
      refine ⟨γ, ?_, ?_⟩
      · simpa [γ, i, i₀, a, a₀] using congrArg (fun k => k.left.left) hlift
      · simpa [γ, x₀, z, zHom] using congrArg (fun k => k.left) lift.w
    let : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian g
    let : LocallyOfFiniteType f := AlgebraicGeometry.locallyOfFiniteType_of_comp f g
    have hcrit := InfinitesimalLifting.infinitesimal_lifting_criterion_for_smoothness f u₀
    exact (hcrit.out 4 1).mp hres

end Deformation.Artin
