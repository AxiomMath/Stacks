module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.CompactificationData
public import
  StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ProperPushforwardCoherent
public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ExtensionByZeroOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Duality.SeparatedFiniteTypeProper
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemExistence
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictionHomColimit

/-!
# Inverse systems of distinguished triangles computing compactly supported cohomology

Let `f : X ⟶ Y` be a morphism of `FTS_S` and let `K ⟶ L ⟶ M ⟶ K[1]` be a distinguished
triangle of `D^b_{Coh}(𝒪_X)`. [Stacks, Tag 0G52] produces an inverse system of distinguished
triangles

`K_n ⟶ L_n ⟶ M_n ⟶ K_n[1]`

of `D^b_{Coh}(𝒪_Y)` whose three vertex systems give the pro-objects `Rf_! K`, `Rf_! L` and
`Rf_! M`.

The source's proof is two steps. Choose a compactification `j : X ⟶ X̄` over `Y`, with structure
morphism `f̄ : X̄ ⟶ Y`, so that `Rf_! = Rf̄_* ∘ Rj_!`. First apply [Stacks, Tag 0G4M] to `j` and
the given triangle: it produces an inverse system of distinguished triangles
`K̄_n ⟶ L̄_n ⟶ M̄_n ⟶ K̄_n[1]` of `D^b_{Coh}(𝒪_{X̄})` whose vertex systems give `Rj_! K`, `Rj_! L`
and `Rj_! M`. Then put `K_n = Rf̄_* K̄_n`, and likewise for `L_n` and `M_n`. That these give
`Rf_! K`, `Rf_! L` and `Rf_! M` is, as the source puts it, the very definition of `Rf_!`: the
pro-object of a termwise pushed-forward inverse sequence is the pushforward of the pro-object of
the sequence, which is `CategoryTheory.ProSeq.mapOfIso`.

Both steps are proved here. The second is categorical: for a compactification in the sense of
`CategoryTheory.CompactificationData` — the data one compactification contributes to the
construction of `Rf_!`, as in [Stacks, Tag 0G50] — an inverse system of triangles over `X̄` of the
kind [Stacks, Tag 0G4M] provides, `CategoryTheory.CompactificationData.TriangleExtension`, is
pushed forward termwise. The first is [Stacks, Tag 0G4M] itself,
`AlgebraicGeometry.DeligneTriangle.exists_deligneSystem_distTriang_boundedCoherent`, whose vertex
systems are Deligne systems; such a system satisfies [Stacks, Tag 0G2H] and restricts to the
constant system at its value, so its pro-object is `Rj_!` of that value,
`CategoryTheory.ProSeq.isoExtensionByZero`. For the compactification
`CategoryTheory.CompactificationData.ofOpenImmersion` of an open immersion `j : X ⟶ X̄` into a
scheme `X̄` proper over a Noetherian `Y` this gives `TriangleExtension`, and with it the tag.

## Main definitions

* `CategoryTheory.CompactificationData.pushforwardTriangleSystem`: the inverse system
  `(Rf̄_* K̄_n ⟶ Rf̄_* L̄_n ⟶ Rf̄_* M̄_n ⟶ Rf̄_* K̄_n[1])` of triangles of `D^b_{Coh}(𝒪_Y)`.
* `CategoryTheory.CompactificationData.TriangleExtension`: the conclusion of [Stacks, Tag 0G4M] for
  the open immersion of the compactification.
* `CategoryTheory.CompactificationData.ofOpenImmersion`: the compactification attached to an open
  immersion `j : X ⟶ X̄` and a proper morphism `f̄ : X̄ ⟶ Y` to a Noetherian scheme: `Rj_!` is
  `AlgebraicGeometry.extensionByZeroOpenImmersion j` of [Stacks, Tag 0G4N] and `Rf̄_*` is
  `AlgebraicGeometry.properPushforwardBoundedCoherent f̄`.
* `AlgebraicGeometry.lowerShriek`: the functor `Rf_!` of [Stacks, Section 0G4Z] of a morphism of
  `FTS_S` and a compactification of it.

## Main results

* `CategoryTheory.CompactificationData.shriekImageProIso`: an inverse sequence over `X̄` whose
  pro-object is `Rj_! K` has termwise pushforward whose pro-object is `Rf_! K`.
* `CategoryTheory.CompactificationData.exists_shriekImage_distTriang_system`: the categorical step.
* `CategoryTheory.ProSeq.isoExtensionByZero`: an inverse sequence with constant restriction `K`
  satisfying [Stacks, Tag 0G2H] has pro-object `Rj_! K`.
* `AlgebraicGeometry.DeligneTriangle.exists_extensionByZero_distTriang`: [Stacks, Tag 0G4M] with
  the vertex systems identified with `Rj_! K`, `Rj_! L` and `Rj_! M`.
* `CategoryTheory.CompactificationData.triangleExtension_ofOpenImmersion`: hence
  `TriangleExtension` for the compactification of an open immersion.
* `AlgebraicGeometry.exists_shriekImage_distTriang_system`: a distinguished triangle of
  `D^b_{Coh}(𝒪_X)` is computed under `Rf_!` by an inverse system of distinguished triangles of
  `D^b_{Coh}(𝒪_Y)`.

## Implementation notes

**What `Rf_!` is.** As in the rest of the section, `Rf_!` is
`CategoryTheory.CompactificationData.shriekImage` of a compactification, here
`CategoryTheory.CompactificationData.ofOpenImmersion j f̄`: the restriction is
`AlgebraicGeometry.restrictBoundedCoherentLift j`, `Rj_!` is the extension by zero
`AlgebraicGeometry.extensionByZeroOpenImmersion j` of [Stacks, Tag 0G4N], and `Rf̄_*` is the
derived direct image `AlgebraicGeometry.properPushforwardBoundedCoherent f̄`, which preserves
`D^b_{Coh}` because `f̄` is proper ([Stacks, Tag 08E2]) and is exact. It is applied to pro-objects
termwise, `CategoryTheory.ProSeq.map`. For a morphism `f : X ⟶ Y` of `FTS_S` and a compactification
`c` of `X` over `Y` this is `AlgebraicGeometry.lowerShriek f c`. By [Stacks, Tag 0G50] the result
does not depend on the compactification.

**Why the vertex systems need no comparison.** The system of triangles produced is the termwise
image `TM ⋙ Rf̄_*.mapTriangle`, and the first vertex of the image of a triangle under
`CategoryTheory.Functor.mapTriangle` is the image of its first vertex; so the vertex systems of
the image system are the termwise images of the vertex systems, on the nose rather than up to
isomorphism. This is what makes `CategoryTheory.ProSeq.mapOfIso` directly applicable.

**Which derived category.** The scheme-level part installs `HasDerivedCategory.standard` as a
local instance at priority 10000, as
`StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTriangleExtension` does,
so that `D^b_{Coh}` here is the category in which [Stacks, Tag 0G4M] is stated.

## References

* [Stacks Project, Tag 0G52](https://stacks.math.columbia.edu/tag/0G52)
* [Stacks Project, Tag 0G4M](https://stacks.math.columbia.edu/tag/0G4M)
* [Stacks Project, Tag 0G50](https://stacks.math.columbia.edu/tag/0G50)
* [Stacks Project, Tag 0G4N](https://stacks.math.columbia.edu/tag/0G4N)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 0G4L](https://stacks.math.columbia.edu/tag/0G4L)
* [Stacks Project, Tag 08E2](https://stacks.math.columbia.edu/tag/08E2)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u₁ u₂ u₃

namespace CategoryTheory.CompactificationData

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒟 : Type u₂} [Category.{v} 𝒟]
  {ℳ : Type u₃} [Category.{v} ℳ] [HasShift ℳ ℤ] [HasShift 𝒟 ℤ]

/-- The termwise image under the proper pushforward `Rf̄_*` of an inverse system of triangles of
`D^b_{Coh}(𝒪_{X̄})`: the inverse system `(Rf̄_* K̄_n ⟶ Rf̄_* L̄_n ⟶ Rf̄_* M̄_n ⟶ Rf̄_* K̄_n[1])` of
triangles of `D^b_{Coh}(𝒪_Y)`. -/
public def pushforwardTriangleSystem (C : CompactificationData 𝒞 𝒟 ℳ) [C.direct.CommShift ℤ]
    (TM : ℕᵒᵖ ⥤ Triangle ℳ) : ℕᵒᵖ ⥤ Triangle 𝒟 :=
  TM ⋙ C.direct.mapTriangle

/-- The first vertex system of the pushed-forward system of triangles is the termwise pushforward
of the first vertex system. -/
public lemma pushforwardTriangleSystem_comp_π₁ (C : CompactificationData 𝒞 𝒟 ℳ)
    [C.direct.CommShift ℤ] (TM : ℕᵒᵖ ⥤ Triangle ℳ) :
    pushforwardTriangleSystem C TM ⋙ Triangle.π₁ = (TM ⋙ Triangle.π₁) ⋙ C.direct :=
  rfl

/-- The second vertex system of the pushed-forward system of triangles is the termwise pushforward
of the second vertex system. -/
public lemma pushforwardTriangleSystem_comp_π₂ (C : CompactificationData 𝒞 𝒟 ℳ)
    [C.direct.CommShift ℤ] (TM : ℕᵒᵖ ⥤ Triangle ℳ) :
    pushforwardTriangleSystem C TM ⋙ Triangle.π₂ = (TM ⋙ Triangle.π₂) ⋙ C.direct :=
  rfl

/-- The third vertex system of the pushed-forward system of triangles is the termwise pushforward
of the third vertex system. -/
public lemma pushforwardTriangleSystem_comp_π₃ (C : CompactificationData 𝒞 𝒟 ℳ)
    [C.direct.CommShift ℤ] (TM : ℕᵒᵖ ⥤ Triangle ℳ) :
    pushforwardTriangleSystem C TM ⋙ Triangle.π₃ = (TM ⋙ Triangle.π₃) ⋙ C.direct :=
  rfl

/-- **An inverse sequence giving `Rj_! K` has termwise pushforward giving `Rf_! K`.** This is the
"very definition of `Rf_!`" of [Stacks, Tag 0G52]: the functor `Rf_! = Rf̄_* ∘ Rj_!` applies
`Rf̄_*` to pro-objects, and on the pro-object of an inverse sequence that is the pro-object of the
termwise image sequence, `CategoryTheory.ProSeq.mapOfIso`. -/
public def shriekImageProIso (C : CompactificationData 𝒞 𝒟 ℳ)
    [∀ A : ℳ ⥤ Type v, C.direct.HasLeftKanExtension A] {MM : ℕᵒᵖ ⥤ ℳ} {K : 𝒞}
    (e : ProSeq.of MM ≅ (extensionByZero C.restrict C.assignment).obj K) :
    ProSeq.of (MM ⋙ C.direct) ≅ C.shriekImage.obj K :=
  (ProSeq.mapOfIso C.direct MM).symm ≪≫ (ProSeq.map C.direct).mapIso e

variable [HasZeroObject ℳ] [Preadditive ℳ] [∀ n : ℤ, (shiftFunctor ℳ n).Additive]
  [Pretriangulated ℳ] [HasZeroObject 𝒟] [Preadditive 𝒟]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]

/-- Every triangle of the pushed-forward system is distinguished, because `Rf̄_*` is an exact
functor of triangulated categories. -/
public lemma pushforwardTriangleSystem_distinguished (C : CompactificationData 𝒞 𝒟 ℳ)
    [C.direct.Additive] [C.direct.CommShift ℤ] [C.direct.IsTriangulated]
    {TM : ℕᵒᵖ ⥤ Triangle ℳ} (hTM : ∀ n, TM.obj n ∈ distTriang ℳ) (n : ℕᵒᵖ) :
    (pushforwardTriangleSystem C TM).obj n ∈ distTriang 𝒟 :=
  C.direct.map_distinguished _ (hTM n)

variable [HasZeroObject 𝒞] [Preadditive 𝒞] [HasShift 𝒞 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒞 n).Additive] [Pretriangulated 𝒞]

/-- **The conclusion of [Stacks, Tag 0G4M] for the open immersion `j : X ⟶ X̄` of a
compactification**: every distinguished triangle `K ⟶ L ⟶ M ⟶ K[1]` of `D^b_{Coh}(𝒪_X)` is given
by an inverse system of distinguished triangles of `D^b_{Coh}(𝒪_{X̄})` whose three vertex systems
give the pro-objects `Rj_! K`, `Rj_! L` and `Rj_! M`.

In the source these systems are the Deligne systems of the three objects; the scheme-theoretic
construction is
`AlgebraicGeometry.DeligneTriangle.exists_deligneSystem_distTriang_boundedCoherent`. -/
public def TriangleExtension (C : CompactificationData 𝒞 𝒟 ℳ) : Prop :=
  ∀ T : Triangle 𝒞, T ∈ distTriang 𝒞 →
    ∃ TM : ℕᵒᵖ ⥤ Triangle ℳ, (∀ n, TM.obj n ∈ distTriang ℳ) ∧
      Nonempty (ProSeq.of (TM ⋙ Triangle.π₁) ≅
        (extensionByZero C.restrict C.assignment).obj T.obj₁) ∧
      Nonempty (ProSeq.of (TM ⋙ Triangle.π₂) ≅
        (extensionByZero C.restrict C.assignment).obj T.obj₂) ∧
      Nonempty (ProSeq.of (TM ⋙ Triangle.π₃) ≅
        (extensionByZero C.restrict C.assignment).obj T.obj₃)

/-- **The categorical step of [Stacks, Tag 0G52].** For a compactification `j : X ⟶ X̄` over `Y`
with exact pushforward `Rf̄_*`, an inverse system of distinguished triangles of
`D^b_{Coh}(𝒪_{X̄})` whose vertex systems give `Rj_! K`, `Rj_! L` and `Rj_! M` — which is what
[Stacks, Tag 0G4M] provides, in the form `CategoryTheory.CompactificationData.TriangleExtension` —
is sent by `Rf̄_*` to an inverse system of distinguished triangles of `D^b_{Coh}(𝒪_Y)` whose
vertex systems give `Rf_! K`, `Rf_! L` and `Rf_! M`.

The system produced is the termwise image under `Rf̄_*`; its triangles are distinguished because
`Rf̄_*` is exact, and its vertex systems give `Rf_! K`, `Rf_! L` and `Rf_! M` by the very
definition of `Rf_!`. For schemes the input `hC` is discharged by
`AlgebraicGeometry.DeligneTriangle.exists_extensionByZero_distTriang`, and the tag is
`AlgebraicGeometry.exists_shriekImage_distTriang_system`. -/
public theorem exists_shriekImage_distTriang_system (C : CompactificationData 𝒞 𝒟 ℳ)
    [C.direct.Additive] [C.direct.CommShift ℤ] [C.direct.IsTriangulated]
    [∀ A : ℳ ⥤ Type v, C.direct.HasLeftKanExtension A] (hC : C.TriangleExtension) (T : Triangle 𝒞)
    (hT : T ∈ distTriang 𝒞) :
    ∃ TY : ℕᵒᵖ ⥤ Triangle 𝒟, (∀ n, TY.obj n ∈ distTriang 𝒟) ∧
      Nonempty (ProSeq.of (TY ⋙ Triangle.π₁) ≅ C.shriekImage.obj T.obj₁) ∧
      Nonempty (ProSeq.of (TY ⋙ Triangle.π₂) ≅ C.shriekImage.obj T.obj₂) ∧
      Nonempty (ProSeq.of (TY ⋙ Triangle.π₃) ≅ C.shriekImage.obj T.obj₃) := by
  obtain ⟨TM, hTM, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := hC T hT
  exact ⟨pushforwardTriangleSystem C TM, pushforwardTriangleSystem_distinguished C hTM,
    ⟨shriekImageProIso C e₁⟩, ⟨shriekImageProIso C e₂⟩, ⟨shriekImageProIso C e₃⟩⟩

end CategoryTheory.CompactificationData

namespace CategoryTheory

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒟 : Type u₂} [Category.{v} 𝒟]

/-- **An inverse sequence with constant restriction satisfying [Stacks, Tag 0G2H] gives `Rj_! K`.**
If `(F_n)` restricts along `j^*` to the constant system at `K`, and `j^*` identifies
`colim_n Mor(F_n, N)` with `colim_n Mor(j^* F_n, j^* N)` for every `N`, then the pro-object of
`(F_n)` is `Rj_! K` for any Deligne system assignment: both have the functor of points
`N ↦ Mor(K, j^* N)`. This is the uniqueness of [Stacks, Tag 0G4L] (3), in the form used to identify
the vertex systems of [Stacks, Tag 0G4M] with `Rj_!`. -/
public def ProSeq.isoExtensionByZero {jstar : 𝒟 ⥤ 𝒞} (A : DeligneSystemAssignment jstar)
    {F : ℕᵒᵖ ⥤ 𝒟} {K : 𝒞} (e : F ⋙ jstar ≅ (Functor.const ℕᵒᵖ).obj K)
    (hF : ∀ N, RestrictionLifting F jstar N) :
    ProSeq.of F ≅ (extensionByZero jstar A).obj K :=
  ProSeq.isoOfSeqHomColimIso
      (restrictHomIso F jstar K e hF ≪≫ A.homIso K ≪≫ Pro.seqHomColimIso (A.system K)) ≪≫
    (extensionByZeroIso jstar A K).symm

end CategoryTheory

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

variable {U X : Scheme.{u}}

/-- The restriction to `U` of a vertex system of an inverse system of triangles over `X`, when the
restricted system of triangles is constant at `T`, is the constant system at the corresponding
vertex of `T`. -/
private def vertexRestrictIso (j : U ⟶ X) [IsOpenImmersion j] [IsLocallyNoetherian X]
    {TX : ℕᵒᵖ ⥤ Triangle (BoundedCoherentDerived X)} {T : Triangle (BoundedCoherentDerived U)}
    (eR : TX ⋙ (restrictBoundedCoherentLift j).mapTriangle ≅ (Functor.const ℕᵒᵖ).obj T)
    (π : Triangle (BoundedCoherentDerived X) ⥤ BoundedCoherentDerived X)
    (π' : Triangle (BoundedCoherentDerived U) ⥤ BoundedCoherentDerived U)
    (w : π ⋙ restrictBoundedCoherentLift j ≅ (restrictBoundedCoherentLift j).mapTriangle ⋙ π') :
    (TX ⋙ π) ⋙ restrictBoundedCoherentLift j ≅ (Functor.const ℕᵒᵖ).obj (π'.obj T) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft TX w ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight eR π' ≪≫ Functor.constComp _ _ _

/-- **[Stacks, Tag 0G4M] for the extension by zero `Rj_!`.** Let `j : U ⟶ X` be an open immersion
into a Noetherian scheme and let `K ⟶ L ⟶ M ⟶ K[1]` be a distinguished triangle of
`D^b_{Coh}(𝒪_U)`. Then there is an inverse system of distinguished triangles of
`D^b_{Coh}(𝒪_X)` whose three vertex systems give the pro-objects `Rj_! K`, `Rj_! L` and `Rj_! M`,
for any Deligne system assignment defining `Rj_!` ([Stacks, Tag 0G4N]).

The system is that of
`AlgebraicGeometry.DeligneTriangle.exists_deligneSystem_distTriang_boundedCoherent`: its vertex
systems are Deligne systems, hence satisfy [Stacks, Tag 0G2H]
(`AlgebraicGeometry.DeligneSystem.restrictionLifting_lift`), and their restrictions to `U` are the
constant systems at `K`, `L` and `M`; so their pro-objects are `Rj_! K`, `Rj_! L` and `Rj_! M` by
`CategoryTheory.ProSeq.isoExtensionByZero`. -/
public theorem DeligneTriangle.exists_extensionByZero_distTriang (j : U ⟶ X) [IsOpenImmersion j]
    [IsNoetherian X] (A : DeligneSystemAssignment (restrictBoundedCoherentLift j))
    (T : Triangle (BoundedCoherentDerived U)) (hT : T ∈ distTriang (BoundedCoherentDerived U)) :
    ∃ TX : ℕᵒᵖ ⥤ Triangle (BoundedCoherentDerived X),
      (∀ n, TX.obj n ∈ distTriang (BoundedCoherentDerived X)) ∧
      Nonempty (ProSeq.of (TX ⋙ Triangle.π₁) ≅
        (extensionByZero (restrictBoundedCoherentLift j) A).obj T.obj₁) ∧
      Nonempty (ProSeq.of (TX ⋙ Triangle.π₂) ≅
        (extensionByZero (restrictBoundedCoherentLift j) A).obj T.obj₂) ∧
      Nonempty (ProSeq.of (TX ⋙ Triangle.π₃) ≅
        (extensionByZero (restrictBoundedCoherentLift j) A).obj T.obj₃) := by
  obtain ⟨DK, DL, DM, TX, hTX, ⟨eK⟩, ⟨eL⟩, ⟨eM⟩, ⟨eR⟩⟩ :=
    DeligneTriangle.exists_deligneSystem_distTriang_boundedCoherent j T hT
  set R := restrictBoundedCoherentLift j with hR
  have w : ∀ (π : Triangle (BoundedCoherentDerived X) ⥤ BoundedCoherentDerived X)
      (π' : Triangle (BoundedCoherentDerived U) ⥤ BoundedCoherentDerived U)
      (_ : π ⋙ R ≅ R.mapTriangle ⋙ π') (D : DeligneSystem j) (_ : TX ⋙ π ≅ D.system),
      Nonempty (ProSeq.of (TX ⋙ π) ≅ (extensionByZero R A).obj (π'.obj T)) :=
    fun π π' w D e => ⟨ProSeq.isoExtensionByZero A (vertexRestrictIso j eR π π' w)
      (fun N => RestrictionLifting.of_natIso e R N (D.restrictionLifting_lift N))⟩
  refine ⟨TX, hTX, w Triangle.π₁ Triangle.π₁ ?_ DK eK, w Triangle.π₂ Triangle.π₂ ?_ DL eL,
    w Triangle.π₃ Triangle.π₃ ?_ DM eM⟩ <;>
  exact NatIso.ofComponents (fun _ => Iso.refl _)
    (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm)

variable {X' Y : Scheme.{u}}

/-- The ambient scheme of a compactification of a scheme over a Noetherian base is Noetherian: it
is proper over the base, hence of finite type over it, so locally Noetherian, and quasi-compact
over a quasi-compact scheme. -/
public instance CompactificationOf.isNoetherian_space {B : Scheme.{u}} [IsNoetherian B]
    {X₀ : Over B} (c : CompactificationOf X₀) : IsNoetherian c.space :=
  have : IsLocallyNoetherian c.space := LocallyOfFiniteType.isLocallyNoetherian (Y := B) c.toBase
  have : CompactSpace c.space := QuasiCompact.compactSpace_of_compactSpace (Y := B) c.toBase
  {}

/-- **The compactification attached to an open immersion** `j : X ⟶ X̄` and a proper morphism
`f̄ : X̄ ⟶ Y` to a Noetherian scheme. The restriction is
`j^* : D^b_{Coh}(𝒪_{X̄}) ⥤ D^b_{Coh}(𝒪_X)`; `Rj_!` is the extension by zero
`AlgebraicGeometry.extensionByZeroOpenImmersion j` of [Stacks, Tag 0G4N], given by the Deligne
system assignment `AlgebraicGeometry.DeligneSystem.values j` of [Stacks, Tag 0G4L] (2) and
[Stacks, Tag 0G2H]; and `Rf̄_*` is the derived direct image
`AlgebraicGeometry.properPushforwardBoundedCoherent f̄` on bounded coherent derived categories,
[Stacks, Tag 08E2]. Its functor `CategoryTheory.CompactificationData.shriekImage` is the functor
`Rf_! = Rf̄_* ∘ Rj_!` of [Stacks, Section 0G4Z]. -/
public abbrev _root_.CategoryTheory.CompactificationData.ofOpenImmersion (j : X ⟶ X')
    [IsOpenImmersion j] [IsNoetherian X'] (fbar : X' ⟶ Y) [IsProper fbar] [IsNoetherian Y] :
    CompactificationData (BoundedCoherentDerived X) (BoundedCoherentDerived Y)
      (BoundedCoherentDerived X') where
  restrict := restrictBoundedCoherentLift j
  assignment := (DeligneSystem.values j).toAssignment
  direct := properPushforwardBoundedCoherent fbar

/-- **`Rf_! = Rf̄_* ∘ Rj_!`** for the compactification of an open immersion: the extension by zero
of [Stacks, Tag 0G4N] followed by the termwise derived direct image of pro-objects. -/
public lemma _root_.CategoryTheory.CompactificationData.shriekImage_ofOpenImmersion (j : X ⟶ X')
    [IsOpenImmersion j] [IsNoetherian X'] (fbar : X' ⟶ Y) [IsProper fbar] [IsNoetherian Y] :
    (CompactificationData.ofOpenImmersion j fbar).shriekImage =
      extensionByZeroOpenImmersion j ⋙ ProSeq.map (properPushforwardBoundedCoherent fbar) :=
  rfl

/-- **[Stacks, Tag 0G4M] for the open immersion of a compactification**, in the form
`CategoryTheory.CompactificationData.TriangleExtension`: every distinguished triangle of
`D^b_{Coh}(𝒪_X)` is given by an inverse system of distinguished triangles of
`D^b_{Coh}(𝒪_{X̄})` whose vertex systems give `Rj_! K`, `Rj_! L` and `Rj_! M`. -/
public theorem _root_.CategoryTheory.CompactificationData.triangleExtension_ofOpenImmersion
    (j : X ⟶ X') [IsOpenImmersion j] [IsNoetherian X'] (fbar : X' ⟶ Y) [IsProper fbar]
    [IsNoetherian Y] : (CompactificationData.ofOpenImmersion j fbar).TriangleExtension :=
  fun T hT => DeligneTriangle.exists_extensionByZero_distTriang j _ T hT

section FTS

variable {S : Scheme.{u}} [IsNoetherian S] {X₁ Y₁ : FTS S}

/-- **The functor `Rf_!` of [Stacks, Section 0G4Z].** In Situation [Stacks, Tag 0F42] let
`f : X ⟶ Y` be a morphism of `FTS_S` and let `c` be a compactification `j : X ⟶ X̄` of `X` over
`Y`, with structure morphism `f̄ : X̄ ⟶ Y`. Then

`Rf_! = Rf̄_* ∘ Rj_! : D^b_{Coh}(𝒪_X) ⥤ Pro-D^b_{Coh}(𝒪_Y)`,

where `Rj_!` is the extension by zero of [Stacks, Tag 0G4N] and `Rf̄_*` is the derived direct
image, applied to pro-objects termwise. A compactification exists by [Stacks, Tag 0F41] and
[Stacks, Tag 0A9Z]; by [Stacks, Tag 0G50] the functor does not depend on it up to isomorphism. -/
public abbrev lowerShriek (f : X₁ ⟶ Y₁) (c : CompactificationOf (Over.mk f.left)) :
    BoundedCoherentDerived X₁.left ⥤ ProSeq (BoundedCoherentDerived Y₁.left) :=
  (CompactificationData.ofOpenImmersion c.immersion c.toBase).shriekImage

/-- In Situation [Stacks, Tag 0F42] let `f : X ⟶ Y` be a morphism of `FTS_S` and let

`K ⟶ L ⟶ M ⟶ K[1]`

be a distinguished triangle of `D^b_{Coh}(𝒪_X)`. Then there is an inverse system of distinguished
triangles

`K_n ⟶ L_n ⟶ M_n ⟶ K_n[1]`

of `D^b_{Coh}(𝒪_Y)` such that the pro-systems `(K_n)`, `(L_n)` and `(M_n)` give `Rf_! K`,
`Rf_! L` and `Rf_! M`.

Here `Rf_! = Rf̄_* ∘ Rj_!` is `AlgebraicGeometry.lowerShriek f c`, the functor of
[Stacks, Section 0G4Z] attached to a compactification `c`, `j : X ⟶ X̄`, of `X` over `Y` with
structure morphism `f̄ : X̄ ⟶ Y`: `Rj_!` is the extension by zero of [Stacks, Tag 0G4N] and `Rf̄_*`
is the derived direct image `D^b_{Coh}(𝒪_{X̄}) ⥤ D^b_{Coh}(𝒪_Y)`, applied termwise to
pro-objects. The statement holds for every compactification; by [Stacks, Tag 0G50] the functor
does not depend on it.

The proof is the source's. [Stacks, Tag 0G4M] for `j`
(`AlgebraicGeometry.DeligneTriangle.exists_extensionByZero_distTriang`) gives an inverse system of
distinguished triangles `K̄_n ⟶ L̄_n ⟶ M̄_n ⟶ K̄_n[1]` of `D^b_{Coh}(𝒪_{X̄})` whose vertex systems
give `Rj_! K`, `Rj_! L` and `Rj_! M`; the system `K_n = Rf̄_* K̄_n`, and likewise for `L_n` and
`M_n`, works by the very definition of `Rf_!`
(`CategoryTheory.CompactificationData.exists_shriekImage_distTriang_system`). -/
@[stacks 0G52]
public theorem exists_shriekImage_distTriang_system (f : X₁ ⟶ Y₁)
    (c : CompactificationOf (Over.mk f.left)) (T : Triangle (BoundedCoherentDerived X₁.left))
    (hT : T ∈ distTriang (BoundedCoherentDerived X₁.left)) :
    ∃ TY : ℕᵒᵖ ⥤ Triangle (BoundedCoherentDerived Y₁.left),
      (∀ n, TY.obj n ∈ distTriang (BoundedCoherentDerived Y₁.left)) ∧
      Nonempty (ProSeq.of (TY ⋙ Triangle.π₁) ≅ (lowerShriek f c).obj T.obj₁) ∧
      Nonempty (ProSeq.of (TY ⋙ Triangle.π₂) ≅ (lowerShriek f c).obj T.obj₂) ∧
      Nonempty (ProSeq.of (TY ⋙ Triangle.π₃) ≅ (lowerShriek f c).obj T.obj₃) :=
  (CompactificationData.ofOpenImmersion c.immersion c.toBase).exists_shriekImage_distTriang_system
    (CompactificationData.triangleExtension_ofOpenImmersion c.immersion c.toBase) T hT

end FTS

end AlgebraicGeometry

end
