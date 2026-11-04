module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.LowerShriekComposition
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekEtale
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward

/-!
# Covariance of compactly supported cohomology for open immersions and étale morphisms

In Situation [Stacks, Tag 0F42] let `f : X ⟶ Y` be a morphism of `FTS_S`.

* For an open `U ⊆ X` and `g = f|_U` there is a canonical morphism `Rg_!(K|_U) ⟶ Rf_! K`,
  functorial in `K` in `D^b_{Coh}(𝒪_X)` ([Stacks, Tag 0G56]).
* More generally, for an étale `h : U ⟶ X` and `g = f ∘ h` there is a canonical morphism
  `Rg_!(h^* K) ⟶ Rf_! K`, functorial in `K` ([Stacks, Tag 0G57]).

Both are defined as in the source: a morphism of pro-objects into which every `L` of
`D^b_{Coh}(𝒪_Y)` maps is the same as a transformation of the functors `Hom(-, L)` ([Stacks, Tag
0G2X]), and by [Stacks, Tag 0G51] the transformation is

`Hom(Rf_! K, L) = Hom_X(K, f^! L) ⟶ Hom_U(h^* K, h^* f^! L) = Hom_U(h^* K, g^! L)
  = Hom(Rg_!(h^* K), L)`,

with `g^! = j^* ∘ f^!` by the construction of `f^!` for an open immersion `j`, and
`h^* f^! = h^! f^! = g^!` by [Stacks, Tag 0FWI] and [Stacks, Tag 0ATX] for `h` étale.

## Main definitions

* `CategoryTheory.ProSeq.natTransOfPointsFunctor`: a transformation of the functors of points of
  the values of `G` and `G'` is a transformation `G' ⟶ G`.
* `CategoryTheory.homMapNatTrans`: the transformation `Hom(A, F₁ -) ⟶ Hom(H A, F₂ -)` induced by a
  functor `H` and an identification `H ∘ F₁ ≅ F₂`.
* `AlgebraicGeometry.lowerShriekMapOfHom`: a transformation `Rg_! ∘ H ⟶ Rf_!` from a
  transformation of `Hom(-, f^! L)` into `Hom(H -, g^! L)`.
* `AlgebraicGeometry.lowerShriekOpenImmersionMap`: **[Stacks, Tag 0G56]**.
* `AlgebraicGeometry.boundedCoherentPullback`: `h^* : D^b_{Coh}(𝒪_X) ⥤ D^b_{Coh}(𝒪_U)` for `h`
  flat.
* `AlgebraicGeometry.lowerShriekEtaleMap`: **[Stacks, Tag 0G57]**.

## References

* [Stacks Project, Tag 0G56](https://stacks.math.columbia.edu/tag/0G56)
* [Stacks Project, Tag 0G57](https://stacks.math.columbia.edu/tag/0G57)
* [Stacks Project, Tag 0G51](https://stacks.math.columbia.edu/tag/0G51)
* [Stacks Project, Tag 0G2X](https://stacks.math.columbia.edu/tag/0G2X)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory

namespace ProSeq

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒟 : Type u₂} [Category.{v} 𝒟]

/-- **A transformation of functors of points is a transformation of pro-object-valued
functors** ([Stacks, Tag 0G2X]): `Hom(G K, -) ⟶ Hom(G' K, -)` naturally in `K` gives
`G' ⟶ G`. -/
def natTransOfPointsFunctor {G G' : 𝒞 ⥤ ProSeq 𝒟} (τ : pointsFunctor G ⟶ pointsFunctor G') :
    G' ⟶ G where
  app K := (ObjectProperty.homMk (τ.app (op K))).op
  naturality {K K'} k := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact (τ.naturality k.op).symm

/-- On functors of points, `CategoryTheory.ProSeq.natTransOfPointsFunctor τ` is `τ`. -/
theorem natTransOfPointsFunctor_app_unop_hom {G G' : 𝒞 ⥤ ProSeq 𝒟}
    (τ : pointsFunctor G ⟶ pointsFunctor G') (K : 𝒞) :
    ((natTransOfPointsFunctor τ).app K).unop.hom = τ.app (op K) :=
  rfl

end ProSeq

variable {𝒜 : Type u₁} [Category.{v} 𝒜] {𝒜' : Type u₂} [Category.{v} 𝒜']
  {𝒳 : Type u₃} [Category.{v} 𝒳] {𝒳' : Type u₄} [Category.{v} 𝒳'] {ℬ : Type u₅} [Category.{v} ℬ]

/-- The transformation `Hom(ι₁ A, F₁ B) ⟶ Hom(ι₂ (H A), F₂ B)`, `φ ↦ β⁻¹ ≫ Hs φ ≫ θ`, induced by a
functor `Hs` and identifications `β : ι₁ ⋙ Hs ≅ H ⋙ ι₂` and `θ : F₁ ⋙ Hs ≅ F₂`. -/
def homMapNatTrans (ι₁ : 𝒜 ⥤ 𝒳) (ι₂ : 𝒜' ⥤ 𝒳') (H : 𝒜 ⥤ 𝒜') (Hs : 𝒳 ⥤ 𝒳')
    (β : ι₁ ⋙ Hs ≅ H ⋙ ι₂) (F₁ : ℬ ⥤ 𝒳) (F₂ : ℬ ⥤ 𝒳') (θ : F₁ ⋙ Hs ≅ F₂) :
    ι₁.op ⋙ coyoneda ⋙ (Functor.whiskeringLeft _ _ _).obj F₁ ⟶
      H.op ⋙ ι₂.op ⋙ coyoneda ⋙ (Functor.whiskeringLeft _ _ _).obj F₂ where
  app A :=
    { app := fun B => ↾fun φ => β.inv.app A.unop ≫ Hs.map φ ≫ θ.hom.app B
      naturality := fun {B B'} b => by
        ext φ
        change β.inv.app A.unop ≫ Hs.map (φ ≫ F₁.map b) ≫ θ.hom.app B' =
          (β.inv.app A.unop ≫ Hs.map φ ≫ θ.hom.app B) ≫ F₂.map b
        rw [Hs.map_comp, Category.assoc, Category.assoc, Category.assoc]
        exact congrArg (fun t => β.inv.app A.unop ≫ Hs.map φ ≫ t) (θ.hom.naturality b) }
  naturality {A A'} a := by
    ext B φ
    change β.inv.app A'.unop ≫ Hs.map (ι₁.map a.unop ≫ φ) ≫ θ.hom.app B =
      ι₂.map (H.map a.unop) ≫ β.inv.app A.unop ≫ Hs.map φ ≫ θ.hom.app B
    have h := β.inv.naturality a.unop
    simp only [Functor.comp_map] at h
    rw [Hs.map_comp, ← Category.assoc, ← Category.assoc, ← h]
    simp only [Category.assoc]

end CategoryTheory

namespace Stacks.Duality.UpperShriekDuality

open TwistedInverseImageDuality

variable {S : Scheme.{u}} [IsNoetherian S] {U X Y : FTS S}

/-- **`f^!` does not depend on the compactification** ([Stacks, Tag 0AA0]), at the standard
model on `D^+_{Coh}`. -/
def upperShriekStdCompactificationIso (f : X ⟶ Y) (c₁ c₂ : CompactificationOf (Over.mk f.left)) :
    upperShriekStd f c₁ ≅ upperShriekStd f c₂ :=
  Functor.isoWhiskerLeft (plusCohToQCohPlus Y.left)
    (Functor.isoWhiskerRight (DominatingCompactification.upperShriekPlusIso f c₁ c₂)
      (ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (comparison X.left).inverse))

/-- `Lh^* ∘ f^!` at the standard model is `Lh^* ∘ f^!` at the locally small one. -/
def upperShriekStdPullIso (h : U ⟶ X) (f : X ⟶ Y) (c : CompactificationOf (Over.mk f.left)) :
    upperShriekStd f c ⋙ pull h.left ≅
      plusCohToQCoh Y.left ⋙ upperShriek f c ⋙ quasiCoherentDerivedPullback' h.left ⋙
        (ObjectProperty.ι _ : quasiCoherentDerivedCategory U.left ⥤ _) ⋙
          (comparison U.left).inverse :=
  Functor.isoWhiskerLeft (plusCohToQCoh Y.left ⋙ upperShriek f c ⋙
    (ObjectProperty.ι _ : quasiCoherentDerivedCategory X.left ⥤ _)) (pullModelConj h.left).symm

/-- **`g^! = j^* ∘ f^!` for `g = f ∘ j` and an open immersion `j`**, by the construction of the
upper shriek functors ([Stacks, Section 0A9Y], [Stacks, Tag 0AA0]), at the standard model on
`D^+_{Coh}`. -/
def upperShriekStdPrecompOpenIso (j : U ⟶ X) [IsOpenImmersion j.left] (f : X ⟶ Y)
    (c : CompactificationOf (Over.mk f.left)) (cU : CompactificationOf (Over.mk (j ≫ f).left)) :
    upperShriekStd f c ⋙ pull j.left ≅ upperShriekStd (j ≫ f) cU :=
  upperShriekStdPullIso j f c ≪≫
    (Functor.isoWhiskerLeft (plusCohToQCoh Y.left)
      (Functor.isoWhiskerRight (upperShriekPrecompOpenIso j f c).symm
        ((ObjectProperty.ι _ : quasiCoherentDerivedCategory U.left ⥤ _) ⋙
          (comparison U.left).inverse)) :
      plusCohToQCoh Y.left ⋙ upperShriek f c ⋙ quasiCoherentDerivedPullback' j.left ⋙
          (ObjectProperty.ι _ : quasiCoherentDerivedCategory U.left ⥤ _) ⋙
            (comparison U.left).inverse ≅ upperShriekStd (j ≫ f) (c.precompOpen j.left)) ≪≫
    upperShriekStdCompactificationIso (j ≫ f) (c.precompOpen j.left) cU

/-- **`g^! = h^* ∘ f^!` for `g = f ∘ h` and an étale `h`**: `h^* f^! = h^! f^!` by [Stacks, Tag
0FWI] and `h^! f^! = g^!` by [Stacks, Tag 0ATX], for arbitrary compactifications, at the
standard model on `D^+_{Coh}`. -/
def upperShriekStdPullEtaleIso (h : U ⟶ X) [Etale h.left] (f : X ⟶ Y)
    (c : CompactificationOf (Over.mk f.left)) (ch : CompactificationOf (Over.mk h.left))
    (cU : CompactificationOf (Over.mk (h ≫ f).left)) :
    upperShriekStd f c ⋙ pull h.left ≅ upperShriekStd (h ≫ f) cU :=
  upperShriekStdPullIso h f c ≪≫
    (Functor.isoWhiskerLeft (plusCohToQCohPlus Y.left ⋙ upperShriekPlus f c)
      (Functor.isoWhiskerRight (upperShriekIsoPullbackOfEtale h ch).symm
        ((ObjectProperty.ι _ : quasiCoherentDerivedCategory U.left ⥤ _) ⋙
          (comparison U.left).inverse)) :
      plusCohToQCoh Y.left ⋙ upperShriek f c ⋙ quasiCoherentDerivedPullback' h.left ⋙
          (ObjectProperty.ι _ : quasiCoherentDerivedCategory U.left ⥤ _) ⋙
            (comparison U.left).inverse ≅
        plusCohToQCohPlus Y.left ⋙ (upperShriekPlus f c ⋙ upperShriekPlus h ch) ⋙
          ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (comparison U.left).inverse) ≪≫
    (Functor.isoWhiskerLeft (plusCohToQCohPlus Y.left)
      (Functor.isoWhiskerRight (upperShriekCompIso h f ch c cU).symm
        (ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (comparison U.left).inverse)) :
      plusCohToQCohPlus Y.left ⋙ (upperShriekPlus f c ⋙ upperShriekPlus h ch) ⋙
          ObjectProperty.ι _ ⋙ ObjectProperty.ι _ ⋙ (comparison U.left).inverse ≅
        upperShriekStd (h ≫ f) cU)

end Stacks.Duality.UpperShriekDuality

namespace AlgebraicGeometry

open Stacks.Duality Stacks.Duality.TwistedInverseImageDuality Stacks.Duality.UpperShriekDuality

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 10000] CategoryTheory.Functor.hasLeftKanExtension_of_type
  CategoryTheory.Functor.hasPointwiseLeftKanExtension_of_type
attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens
attribute [local instance] Stacks.AssociatedSheaf.abelianModulesRingSheaf

variable {S : Scheme.{u}} [IsNoetherian S] {U X Y : FTS S}

/-- **A transformation `Rg_! ∘ H ⟶ Rf_!` from a transformation of `Hom` functors.** For
`H : D^b_{Coh}(𝒪_X) ⥤ D^b_{Coh}(𝒪_U)` and a transformation
`Hom_X(K, f^! L) ⟶ Hom_U(H K, g^! L)`, natural in `K` and in `L` in `D^+_{Coh}(𝒪_Y)`, the
transformation `Hom(Rf_! K, L) ⟶ Hom(Rg_!(H K), L)` of [Stacks, Tag 0G51] is a transformation of
the functors of points, hence ([Stacks, Tag 0G2X]) a morphism `Rg_!(H K) ⟶ Rf_! K` natural in
`K`. -/
def lowerShriekMapOfHom (f : X ⟶ Y) (c : CompactificationOf (Over.mk f.left)) (g : U ⟶ Y)
    (cU : CompactificationOf (Over.mk g.left))
    (H : BoundedCoherentDerived X.left ⥤ BoundedCoherentDerived U.left)
    (ρ : (boundedCoherentDerived X.left).ι.op ⋙ coyoneda ⋙
        (Functor.whiskeringLeft _ _ _).obj (upperShriekStd f c) ⟶
      H.op ⋙ (boundedCoherentDerived U.left).ι.op ⋙ coyoneda ⋙
        (Functor.whiskeringLeft _ _ _).obj (upperShriekStd g cU)) :
    H ⋙ lowerShriek g cU ⟶ lowerShriek f c :=
  ProSeq.natTransOfPointsFunctor ((lowerShriekPointsFunctorIsoStd f c).hom ≫
    Functor.whiskerRight ρ _ ≫ Functor.whiskerLeft H.op (lowerShriekPointsFunctorIsoStd g cU).inv)

/-- Restriction to an open `U` is `Lj^*` on `D^b_{Coh}`, at the standard model. -/
def restrictBoundedCoherentPullIso (j : U ⟶ X) [IsOpenImmersion j.left] :
    (boundedCoherentDerived X.left).ι ⋙ pull j.left ≅
      restrictBoundedCoherentLift j.left ⋙ (boundedCoherentDerived U.left).ι :=
  NatIso.ofComponents
    (fun K => ((Scheme.Modules.derivedRestrictIsoDerivedPullback j.left).app K.obj).symm)
    (fun φ => (Scheme.Modules.derivedRestrictIsoDerivedPullback j.left).inv.naturality φ.hom)

/-- **Stacks Project, Tag 0G56.** In Situation [Stacks, Tag 0F42] let `f : X ⟶ Y` be a morphism
of `FTS_S`, let `j : U ⟶ X` be an open immersion and `g = f ∘ j = f|_U`. Then there is a
canonical morphism

`Rg_!(K|_U) ⟶ Rf_! K`,

functorial in `K` in `D^b_{Coh}(𝒪_X)`. This is the third construction of the source: for `L` in
`D^b_{Coh}(𝒪_Y)`,

`Hom(Rf_! K, L) = Hom_X(K, f^! L) ⟶ Hom_U(K|_U, (f^! L)|_U) = Hom_U(K|_U, g^! L)
  = Hom(Rg_!(K|_U), L)`,

by [Stacks, Tag 0G51] twice and `g^! = j^* ∘ f^!` (the construction of the upper shriek
functors, `Stacks.Duality.UpperShriekDuality.upperShriekStdPrecompOpenIso`), and the
functoriality in `L` gives the morphism of pro-objects by [Stacks, Tag 0G2X]
(`AlgebraicGeometry.lowerShriekMapOfHom`). `Rf_!` and `Rg_!` are computed at arbitrary
compactifications `c` and `cU`. -/
@[stacks 0G56]
def lowerShriekOpenImmersionMap (f : X ⟶ Y) (c : CompactificationOf (Over.mk f.left))
    (j : U ⟶ X) [IsOpenImmersion j.left] (cU : CompactificationOf (Over.mk (j ≫ f).left)) :
    restrictBoundedCoherentLift j.left ⋙ lowerShriek (j ≫ f) cU ⟶ lowerShriek f c :=
  lowerShriekMapOfHom f c (j ≫ f) cU (restrictBoundedCoherentLift j.left)
    (homMapNatTrans (boundedCoherentDerived X.left).ι (boundedCoherentDerived U.left).ι
      (restrictBoundedCoherentLift j.left) (pull j.left) (restrictBoundedCoherentPullIso j)
      (upperShriekStd f c) (upperShriekStd (j ≫ f) cU) (upperShriekStdPrecompOpenIso j f c cU))

section Flat

variable {U' X' : Scheme.{u}} (h : U' ⟶ X') [Flat h]

attribute [local instance] preservesFiniteLimits_modulesPullback_of_flat
  preservesFiniteColimits_modulesPullback

/-- **Flat pullback preserves `D^b_{Coh}`**: `h^*` is exact, so it commutes with the cohomology
sheaves; it preserves vanishing and carries coherent modules to coherent modules
([Stacks, Tag 0EBF]). -/
theorem mem_boundedCoherentDerived_pullback [IsLocallyNoetherian U']
    (L : DerivedCategory X'.Modules)
    (hL : boundedCoherentDerived X' L) :
    boundedCoherentDerived U' ((Scheme.Modules.pullback h).mapDerivedCategory.obj L) := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ := hL
  have e := fun i => ((Scheme.Modules.pullback h).mapDerivedCategoryHomologyIso i).app L
  refine ⟨⟨⟨a, fun i hi => ?_⟩, ⟨b, fun i hi => ?_⟩⟩, fun i => ?_⟩
  · exact ((Scheme.Modules.pullback h).map_isZero (ha i hi)).of_iso (e i)
  · exact ((Scheme.Modules.pullback h).map_isZero (hb i hi)).of_iso (e i)
  · have : ((DerivedCategory.homologyFunctor X'.Modules i).obj L).IsCoherent := hc i
    exact (coherentInModules U').prop_of_iso (e i).symm (isCoherent_pullback h _)

/-- **`h^* : D^b_{Coh}(𝒪_X) ⥤ D^b_{Coh}(𝒪_U)`** for a flat morphism `h : U ⟶ X` with `U` locally
Noetherian: the exact pullback of modules, on derived categories. -/
abbrev boundedCoherentPullback [IsLocallyNoetherian U'] :
    BoundedCoherentDerived X' ⥤ BoundedCoherentDerived U' :=
  (boundedCoherentDerived U').lift
    ((boundedCoherentDerived X').ι ⋙ (Scheme.Modules.pullback h).mapDerivedCategory)
    fun L => mem_boundedCoherentDerived_pullback h L.obj L.property

/-- For `h` flat, `Lh^*` is `h^*` on `D^b_{Coh}`, at the standard model. -/
def boundedCoherentPullbackPullIso [IsLocallyNoetherian U'] :
    (boundedCoherentDerived X').ι ⋙ pull h ≅
      boundedCoherentPullback h ⋙ (boundedCoherentDerived U').ι :=
  haveI : PreservesFiniteLimits (RingedSpaceModuleAdjunction.modulePullback h.toLRSHom.toShHom) :=
    inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.pullback h))
  haveI : PreservesFiniteColimits
      (RingedSpaceModuleAdjunction.modulePullback h.toLRSHom.toShHom) :=
    inferInstanceAs (PreservesFiniteColimits (Scheme.Modules.pullback h))
  Functor.isoWhiskerLeft (boundedCoherentDerived X').ι
    (AlgebraicGeometry.SpecField.derivedPullbackMapDerivedIso h.toLRSHom.toShHom)

end Flat

/-- **Stacks Project, Tag 0G57.** In Situation [Stacks, Tag 0F42] let

`U --h--> X --f--> Y`,  `g = f ∘ h`

be a commutative diagram of `FTS_S` with `h` étale. Then there is a canonical morphism

`Rg_!(h^* K) ⟶ Rf_! K`,

functorial in `K` in `D^b_{Coh}(𝒪_X)`, defined by the sequence of maps

`Hom(Rf_! K, L) = Hom_X(K, f^! L) ⟶ Hom_U(h^* K, h^*(f^! L)) = Hom_U(h^* K, h^! f^! L)
  = Hom_U(h^* K, g^! L) = Hom(Rg_!(h^* K), L)`

for `L` in `D^b_{Coh}(𝒪_Y)`: [Stacks, Tag 0G51] twice, `h^* = h^!` ([Stacks, Tag 0FWI]) and
`h^! ∘ f^! = g^!` ([Stacks, Tag 0ATX]); the functoriality in `L` gives the morphism of
pro-objects by [Stacks, Tag 0G2X] (`AlgebraicGeometry.lowerShriekMapOfHom`). `Rf_!` and `Rg_!` are
computed at arbitrary compactifications `c` and `cU`, and `h^!` at the compactification of `h`
obtained from them (`Stacks.Duality.CompCompactification.restrictCompactification`). -/
@[stacks 0G57]
def lowerShriekEtaleMap (f : X ⟶ Y) (c : CompactificationOf (Over.mk f.left)) (h : U ⟶ X)
    [Etale h.left] (g : U ⟶ Y) (w : h ≫ f = g) (cU : CompactificationOf (Over.mk g.left)) :
    boundedCoherentPullback h.left ⋙ lowerShriek g cU ⟶ lowerShriek f c := by
  subst w
  exact lowerShriekMapOfHom f c (h ≫ f) cU (boundedCoherentPullback h.left)
    (homMapNatTrans (boundedCoherentDerived X.left).ι (boundedCoherentDerived U.left).ι
      (boundedCoherentPullback h.left) (pull h.left) (boundedCoherentPullbackPullIso h.left)
      (upperShriekStd f c) (upperShriekStd (h ≫ f) cU)
      (upperShriekStdPullEtaleIso h f c (CompCompactification.restrictCompactification h f c cU)
        cU))

end AlgebraicGeometry
