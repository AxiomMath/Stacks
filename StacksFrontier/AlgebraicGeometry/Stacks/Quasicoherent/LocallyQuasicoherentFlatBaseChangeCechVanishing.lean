module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfSheafFlatBaseChangeProved
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.CechVanishingStandardCovering
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.FibreProducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.SliceCoefficientsAlongAFunctor
public import StacksFrontier.CategoryTheory.Sites.Continuous.CoveringPullbacks
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Čech vanishing for a locally quasi-coherent module with the flat base change property

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `F` be a presheaf of
modules over the structure sheaf of **Stacks 06TV** which is locally quasi-coherent
(**Stacks 06WJ**) and has the flat base change property (**Stacks 0762**). Let `x` be an object of
`𝒳` lying over an affine scheme `U`, and let `{x_i → x}` be a family of arrows of `𝒳` lying over a
standard fppf covering `{U_i → U}` of Stacks 03X8 — finitely many affine `U_i`, each flat and of
finite presentation over `U`, jointly surjective. Then

`Ȟ^p({x_i → x}, F) = 0` for `p > 0`.

This is the Čech-cohomological input of the vanishing `H^p(x, F) = 0` for `p > 0` on which the
proofs of **Stacks 075R**, **Stacks 08IY**, **Stacks 0771** (2) and **Stacks 07B8** rest; the
source obtains that vanishing from Descent, **Stacks 0756**, and Cohomology of Schemes,
**Stacks 01XB**.

## The argument

The iterated fibre products `x_{i_0} ×_x … ×_x x_{i_p}` lie over the iterated fibre products
`U_{i_0} ×_U … ×_U U_{i_p}`, which are flat over `U`. Let `𝓕` be the quasi-coherent `𝒪_U`-module
with `𝓕^a ≅ F|_{U_ét}` of the first step of the proof of **Stacks 076T**. Along every arrow
`φ : z ⟶ x` of `𝒳` lying over a flat morphism `g : W ⟶ U` the flat base change property
identifies `F(z)` with `Γ(W, g^*𝓕)`, which is the value at `W / U` of the presheaf `𝓕^a` of
**Stacks 03DS** (`AlgebraicGeometry.Stack.liftedSectionsIso`), compatibly with composition of
such arrows (`AlgebraicGeometry.Stack.LiftedSectionsCocycle`, proved in the library). So the
Čech complex of `F` along `{x_i → x}` is the Čech complex of `𝓕^a` along `{U_i → U}`
(`Stacks.CechSite.sliceCechComplexIsoOfFunctor`), and the latter is exact in positive degrees by
the Amitsur complex of the faithfully flat ring map of the covering,
`AlgebraicGeometry.isZero_cechCohomology_succ_quasiCoherentPresheaf` (**Stacks 03FJ**).

## Main results

* `CategoryTheory.MorphismProperty.prop_hom_piObj_fin`: in the slice of a category with
  pullbacks, the structure morphism of a finite nonempty product of objects whose structure
  morphisms have a property stable under base change and composition again has it.
* `CategoryTheory.Functor.IsFiberedInGroupoids.preservesLimit_cospan`: a category fibred in
  groupoids over a category with pullbacks has its pullbacks preserved by the projection.
* `AlgebraicGeometry.Stack.isZero_cechCohomology_of_lqcFbc`: the Čech vanishing.

## References

* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 0756](https://stacks.math.columbia.edu/tag/0756)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ u₁ u v

namespace CategoryTheory.MorphismProperty

variable {T : Type u₁} [Category.{v₁} T] [HasPullbacks T] (P : MorphismProperty T)
  [P.IsStableUnderBaseChange] [P.IsStableUnderComposition] [P.RespectsIso]

/-- The structure morphism of an object of a slice has a property respecting isomorphisms as soon
as that of an isomorphic object does. -/
private theorem prop_hom_of_iso {C : Type u₁} [Category.{v₁} C] (Q : MorphismProperty C)
    [Q.RespectsIso] {X : C} {Y Z : Over X} (e : Y ≅ Z) (hZ : Q Z.hom) : Q Y.hom := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((CategoryTheory.Over.forget X).map e.hom))
  rw [← CategoryTheory.Over.w e.hom, Q.cancel_left_of_respectsIso]
  exact hZ

/-- **The structure morphism of a binary product in a slice inherits a property stable under base
change and composition.** The binary product is the fibre product over the base, whose structure
morphism is the base change of one structure morphism followed by the other. -/
@[ega "I 3.5.1" "(ii) ⇒ (i), special case",
  ega "I 5.5.12" "special case",
  sga "3 IV 3.4.1" "special case"]
theorem prop_hom_prod {X : T} (Y Z : Over X) [HasBinaryProduct Y Z] (hY : P Y.hom)
    (hZ : P Z.hom) : P (Y ⨯ Z).hom := by
  let c := pullbackConeEquivBinaryFan.functor.obj (pullback.cone Y.hom Z.hom)
  have hc : IsLimit c := (pullback.isLimit Y.hom Z.hom).pullbackConeEquivBinaryFanFunctor
  refine prop_hom_of_iso P ((limit.isLimit _).conePointUniqueUpToIso hc) ?_
  exact P.comp_mem _ _ (P.pullback_fst _ _ hZ) hY

/-- **The structure morphism of a finite nonempty product in a slice inherits a property stable
under base change and composition**, by induction from the binary case: a product over
`Fin (n + 2)` is the binary product of its first factor with the product of the others. -/
@[ega "I 3.5.1" "(ii) ⇒ (i), special case", sga "3 IV 3.4.1" "special case"]
theorem prop_hom_piObj_fin {X : T} :
    ∀ (n : ℕ) (A : Fin (n + 1) → Over X) [HasProduct A], (∀ a, P (A a).hom) →
      P (∏ᶜ A).hom := by
  intro n
  induction n with
  | zero =>
    intro A _ hA
    have : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
    exact prop_hom_of_iso P (productUniqueIso A) (hA _)
  | succ n ih =>
    intro A _ hA
    have hprod : HasProduct (fun i : Fin (n + 1) => A i.succ) :=
      Stacks.Sites.hasProduct_over_fin n _ (fun _ _ _ => inferInstance)
    have hbp : HasBinaryProduct (A 0) (∏ᶜ (fun i : Fin (n + 1) => A i.succ)) :=
      Stacks.Sites.hasBinaryProduct_over_of_hasPullback _ _ inferInstance
    have : HasBinaryProduct (A 0)
        (Fan.mk (∏ᶜ (fun i : Fin (n + 1) => A i.succ))
          (Pi.π (fun i : Fin (n + 1) => A i.succ))).pt := hbp
    refine prop_hom_of_iso P ((limit.isLimit _).conePointUniqueUpToIso
      (extendFanIsLimit A (productIsProduct _) (prodIsProd _ _))) ?_
    exact prop_hom_prod P _ _ (hA 0) (ih _ fun a => hA a.succ)

end CategoryTheory.MorphismProperty

namespace CategoryTheory.Functor.IsFiberedInGroupoids

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒞 : Type u} [Category.{v} 𝒞] [HasPullbacks 𝒞]

/-- **The projection of a category fibred in groupoids preserves fibre products.** Fibre products
exist upstairs because they do downstairs, and the projection carries a pullback square to a
pullback square (Stacks 06N6). -/
theorem preservesLimit_cospan (p : 𝒮 ⥤ 𝒞) (hp : p.IsFiberedInGroupoids) {X Y Z : 𝒮}
    (g : X ⟶ Z) (h : Y ⟶ Z) : PreservesLimit (cospan g h) p := by
  have : HasPullback g h := hp.hasPullback p g h
  have hX : IsPullback (pullback.fst g h) (pullback.snd g h) g h :=
    IsPullback.of_hasPullback g h
  exact preservesLimit_of_preserves_limit_cone hX.isLimit
    ((isLimitMapConePullbackConeEquiv p hX.w).symm (hp.map_isPullback p g h _ _ hX).isLimit)

end CategoryTheory.Functor.IsFiberedInGroupoids

namespace AlgebraicGeometry.Stack

attribute [local implicit_reducible] CategoryTheory.PreZeroHypercover.map

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The functor from a category fibred in groupoids over the big fppf site of `S` to schemes,
sending an object to the scheme it lies over. -/
abbrev toScheme : 𝒳 ⥤ Scheme.{u} := p ⋙ Over.forget (B.obj hS) ⋙ B.inclusion

include hp in
/-- The functor to schemes preserves fibre products: the projection does, as does the passage
from the slice to the size-bounded schemes and from there to all schemes. -/
theorem preservesLimit_cospan_toScheme {X Y Z : 𝒳} (g : X ⟶ Z) (g' : Y ⟶ Z) :
    PreservesLimit (cospan g g') (toScheme B S hS p) := by
  have h₁ := Functor.IsFiberedInGroupoids.preservesLimit_cospan p hp g g'
  have h₂ : PreservesLimitsOfShape WalkingCospan (Over.forget (B.obj hS) ⋙ B.inclusion) :=
    inferInstance
  exact comp_preservesLimit p (Over.forget (B.obj hS) ⋙ B.inclusion)

include hp in
/-- `𝒳` has fibre products. -/
theorem hasPullbacks_fibred : HasPullbacks 𝒳 :=
  BigFppfOver.hasPullbacks_of_isFiberedInGroupoids B S hS p hp

include hp in
/-- **The functor to schemes preserves the iterated fibre products of a family**: the comparison
map from the image of an iterated fibre product of a family of arrows of `𝒳` to the iterated
fibre product of the image family is invertible. -/
theorem isIso_cechProductMapOfFunctor_toScheme {x : 𝒳} (𝒰 : PreZeroHypercover.{u} x)
    [∀ (n : ℕ) (i : Fin (n + 1) → 𝒰.I₀), HasProduct (fun a ↦ Over.mk (𝒰.f (i a)))]
    [∀ (n : ℕ) (i : Fin (n + 1) → (𝒰.map (toScheme B S hS p)).I₀),
      HasProduct (fun a ↦ Over.mk ((𝒰.map (toScheme B S hS p)).f (i a)))]
    (m : ℕ) (i : Fin (m + 1) → 𝒰.I₀) :
    IsIso (Stacks.CechSite.cechProductMapOfFunctor (toScheme B S hS p) 𝒰 m i) := by
  have : HasPullbacks 𝒳 := hasPullbacks_fibred B S hS p hp
  have : PreservesLimit (Discrete.functor (fun a ↦ Over.mk (𝒰.f (i a))))
      (Over.post (toScheme B S hS p)) :=
    Stacks.Sites.preservesLimit_fibreProducts_overPost (toScheme B S hS p) 𝒰
      (fun _ _ _ ↦ inferInstance) (fun _ _ g ↦ preservesLimit_cospan_toScheme B S hS p hp _ g) m i
  exact Stacks.CechSite.isIso_cechProductMapOfFunctor (toScheme B S hS p) 𝒰 m i

include hp in
/-- **An iterated fibre product of a family lies over a morphism with every property of the
members of the family which is stable under base change and composition**: it lies over the
iterated fibre product of the image family, whose structure morphism has the property by
`CategoryTheory.MorphismProperty.prop_hom_piObj_fin`. -/
theorem prop_toScheme_map_cechProduct_hom (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition] [P.RespectsIso]
    {x : 𝒳} (𝒰 : PreZeroHypercover.{u} x)
    [∀ (n : ℕ) (i : Fin (n + 1) → 𝒰.I₀), HasProduct (fun a ↦ Over.mk (𝒰.f (i a)))]
    (hP : ∀ j, P ((toScheme B S hS p).map (𝒰.f j))) (m : ℕ) (i : Fin (m + 1) → 𝒰.I₀) :
    P ((toScheme B S hS p).map (∏ᶜ (fun a ↦ Over.mk (𝒰.f (i a)))).hom) := by
  have hEu : ∀ (m : ℕ) (i : Fin (m + 1) → (𝒰.map (toScheme B S hS p)).I₀),
      HasProduct (fun a ↦ Over.mk ((𝒰.map (toScheme B S hS p)).f (i a))) := fun m i ↦
    Stacks.Sites.hasProduct_over_fin m _ (fun _ _ _ ↦ inferInstance)
  have := isIso_cechProductMapOfFunctor_toScheme B S hS p hp 𝒰 m i
  show P ((Over.post (toScheme B S hS p)).obj (∏ᶜ (fun a ↦ Over.mk (𝒰.f (i a))))).hom
  refine MorphismProperty.prop_hom_of_iso P
    (asIso (Stacks.CechSite.cechProductMapOfFunctor (toScheme B S hS p) 𝒰 m i)) ?_
  exact MorphismProperty.prop_hom_piObj_fin P m _ fun a ↦ hP (i a)

include hp in
/-- **The Čech complex of a presheaf along a family lying over a standard fppf covering of an
affine scheme is exact in positive degrees, as soon as its sections over the objects lying flat
over the scheme below the target are those of a quasi-coherent module.**

Let `x` lie over an affine scheme `U`, let `𝓕` be a quasi-coherent `𝒪_U`-module, and suppose that
for every arrow `z ⟶ x` of `𝒳` lying over a flat morphism `W ⟶ U` the sections `F(z)` are
identified with the sections of the presheaf `𝓕^a` of Stacks 03DS over `W / U`, compatibly with
the restriction maps between such arrows. Then the Čech complex of `F` along a family
`{x_i → x}` lying over a standard fppf covering `{U_i → U}` is the Čech complex of `𝓕^a` along
`{U_i → U}` (`Stacks.CechSite.sliceCechComplexIsoOfFunctor`): the iterated fibre products of the
family lie over the iterated fibre products of the covering, which are flat over `U`. The latter
complex is exact in positive degrees by the Amitsur complex of the faithfully flat ring map of the
covering, `AlgebraicGeometry.isZero_cechCohomology_succ_quasiCoherentPresheaf`
(**Stacks 03FJ**). -/
theorem isZero_cechCohomology_of_flatSectionsIso (F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{u})
    {x : 𝒳} [IsAffine ((toScheme B S hS p).obj x)] (𝓕 : (p.obj x).left.1.Modules)
    [𝓕.IsQuasicoherent]
    (e : ∀ Y : Over x, Flat ((toScheme B S hS p).map Y.hom) →
      (F.obj (op Y.left) ≅ (quasiCoherentPresheafFunctor (p.obj x).left.1 𝓕).obj
        (op ((Over.post (toScheme B S hS p)).obj Y))))
    (he : ∀ {Y Y' : Over x} (hY : Flat ((toScheme B S hS p).map Y.hom))
      (hY' : Flat ((toScheme B S hS p).map Y'.hom)) (g : Y' ⟶ Y),
      F.map g.left.op ≫ (e Y' hY').hom =
        (e Y hY).hom ≫ (quasiCoherentPresheafFunctor (p.obj x).left.1 𝓕).map
          ((Over.post (toScheme B S hS p)).map g).op)
    (𝒰 : PreZeroHypercover.{u} x)
    [∀ (n : ℕ) (i : Fin (n + 1) → 𝒰.I₀), HasProduct (fun a ↦ Over.mk (𝒰.f (i a)))]
    (hstd : IsStandardCovering .fppf (fun i ↦ (toScheme B S hS p).obj (𝒰.X i))
      (fun i ↦ (toScheme B S hS p).map (𝒰.f i)))
    (n : ℕ) (hn : 0 < n) :
    IsZero (Stacks.CechSite.cechCohomology 𝒰 F n) := by
  classical
  have : MorphismProperty.RespectsIso @Flat := MorphismProperty.IsStableUnderBaseChange.respectsIso
  set u := toScheme B S hS p
  have : HasPullbacks 𝒳 := hasPullbacks_fibred B S hS p hp
  -- The iterated fibre products of the image family exist.
  have hEu : ∀ (m : ℕ) (i : Fin (m + 1) → (𝒰.map u).I₀),
      HasProduct (fun a ↦ Over.mk ((𝒰.map u).f (i a))) := fun m i ↦
    Stacks.Sites.hasProduct_over_fin m _ (fun _ _ _ ↦ inferInstance)
  -- `u` preserves the iterated fibre products of the family.
  have hcmp : ∀ (m : ℕ) (i : Fin (m + 1) → 𝒰.I₀),
      IsIso (Stacks.CechSite.cechProductMapOfFunctor u 𝒰 m i) :=
    isIso_cechProductMapOfFunctor_toScheme B S hS p hp 𝒰
  let Q : (Over (u.obj x))ᵒᵖ ⥤ AddCommGrpCat.{u} :=
    quasiCoherentPresheafFunctor (p.obj x).left.1 𝓕
  let K : ObjectProperty (Over x) := fun Y ↦ Flat (u.map Y.hom)
  -- The iterated fibre products lie over flat morphisms.
  have hK : ∀ (m : ℕ) (i : Fin (m + 1) → 𝒰.I₀), K (∏ᶜ (fun a ↦ Over.mk (𝒰.f (i a)))) :=
    prop_toScheme_map_cechProduct_hom B S hS p hp @Flat 𝒰 (fun j ↦ (hstd.standard j).1)
  -- The Čech complex upstairs is the Čech complex of the image family downstairs.
  have e₁ := Stacks.CechSite.sliceCechComplexIsoOfFunctor u 𝒰
    ((Over.forget x).op ⋙ F) Q K e he hK hcmp
  -- The image family, read as a family of the slice of all schemes over `U`.
  let T : Over (u.obj x) := Over.mk (𝟙 (u.obj x))
  have : IsAffine T.left := ‹IsAffine ((toScheme B S hS p).obj x)›
  let 𝒱 : PreZeroHypercover.{u} T :=
    { I₀ := 𝒰.I₀
      X i := Over.mk (u.map (𝒰.f i))
      f i := Over.homMk (u.map (𝒰.f i)) (by simp [T]) }
  have h𝒱 : ∀ (m : ℕ) (i : Fin (m + 1) → 𝒱.I₀), HasProduct (fun a ↦ Over.mk (𝒱.f (i a))) :=
    fun m i ↦ Stacks.Sites.hasProduct_over_fin m _ (fun _ _ _ ↦ inferInstance)
  have hcmp' : ∀ (m : ℕ) (i : Fin (m + 1) → 𝒱.I₀),
      IsIso (Stacks.CechSite.cechProductMapOfFunctor (Over.forget (u.obj x)) 𝒱 m i) :=
    fun m i ↦ by
      have : PreservesLimit (Discrete.functor (fun a ↦ Over.mk (𝒱.f (i a))))
          (Over.post (Over.forget (u.obj x))) :=
        Stacks.Sites.preservesLimit_fibreProducts_overPost (Over.forget (u.obj x)) 𝒱
          (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) m i
      exact Stacks.CechSite.isIso_cechProductMapOfFunctor (Over.forget (u.obj x)) 𝒱 m i
  -- The two readings of the coefficients on the slice of the slice agree.
  let e' : ∀ Y : Over T, (⊤ : ObjectProperty (Over T)) Y →
      (((Over.forget T).op ⋙ Q).obj (op Y) ≅
        Q.obj (op ((Over.post (Over.forget (u.obj x))).obj Y))) := fun Y _ ↦
    Q.mapIso (Iso.op (Over.isoMk (Iso.refl Y.left.left)
      (by
        show 𝟙 _ ≫ Y.left.hom = Y.hom.left
        simpa [T] using (CategoryTheory.Over.w Y.hom).symm) :
        (Over.post (Over.forget (u.obj x))).obj Y ≅ (Over.forget T).obj Y))
  have he' : ∀ {Y Y' : Over T} (hY : (⊤ : ObjectProperty (Over T)) Y)
      (hY' : (⊤ : ObjectProperty (Over T)) Y') (g : Y' ⟶ Y),
      ((Over.forget T).op ⋙ Q).map g.op ≫ (e' Y' hY').hom =
        (e' Y hY).hom ≫ Q.map ((Over.post (Over.forget (u.obj x))).map g).op := by
    intro Y Y' _ _ g
    simp only [e', Functor.comp_map, Functor.op_map, Functor.mapIso_hom, Iso.op_hom,
      ← Functor.map_comp, ← op_comp]
    congr 2
  have e₂ := Stacks.CechSite.sliceCechComplexIsoOfFunctor (Over.forget (u.obj x)) 𝒱
    ((Over.forget T).op ⋙ Q) Q ⊤ e' he' (fun _ _ ↦ trivial) hcmp'
  -- Amitsur: the Čech complex of `𝓕^a` along a standard covering is exact in positive degrees.
  have hstd' : IsStandardCovering .fppf (fun i ↦ (𝒱.X i).left) (fun i ↦ (𝒱.f i).left) := hstd
  have hA := isZero_cechCohomology_succ_quasiCoherentPresheaf T .fppf 𝓕 𝒱 hstd' n hn
  -- Assemble.
  show IsZero ((Stacks.CechSite.sliceCechComplex 𝒰 ((Over.forget x).op ⋙ F)).homology n)
  refine IsZero.of_iso ?_ ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso
    e₁.symm)
  exact IsZero.of_iso hA ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n).mapIso e₂)

variable (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B)).obj)

/-- **The Čech complex of a locally quasi-coherent module with the flat base change property,
along a family of arrows lying over a standard fppf covering of an affine scheme, is exact in
positive degrees.**

This is `AlgebraicGeometry.Stack.isZero_cechCohomology_of_flatSectionsIso` at the quasi-coherent
module `𝓕` below `x` of the first step of the proof of **Stacks 076T**: along an arrow lying over
a flat morphism the flat base change property gives the identification
`AlgebraicGeometry.Stack.liftedSectionsIso`, and its compatibility with the restriction maps is
`AlgebraicGeometry.Stack.LiftedSectionsCocycle`. -/
theorem isZero_cechCohomology_of_lqcFbc
    (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
    (hbc : HasFlatBaseChangeProperty B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) F)
    {x : 𝒳} [IsAffine ((toScheme B S hS p).obj x)] (𝒰 : PreZeroHypercover.{u} x)
    [∀ (n : ℕ) (i : Fin (n + 1) → 𝒰.I₀), HasProduct (fun a ↦ Over.mk (𝒰.f (i a)))]
    (hstd : IsStandardCovering .fppf (fun i ↦ (toScheme B S hS p).obj (𝒰.X i))
      (fun i ↦ (toScheme B S hS p).map (𝒰.f i)))
    (n : ℕ) (hn : 0 < n) :
    IsZero (Stacks.CechSite.cechCohomology 𝒰 F.presheaf n) := by
  obtain ⟨d⟩ := nonempty_quasicoherentBelow B E h S hS p hp F hlqc x
  have := d.isQuasicoherent
  have hcoc : LiftedSectionsCocycle B E h S hS p hp :=
    liftedSectionsCocycle_of_factorFourSquare B E h S hS p hp
      (liftedSectionsFactorFourSquare_of_compat B E h S hS p hp
        (associatedModuleBaseChangeFinalSectionsCompat B E h S hS p hp))
  let e : ∀ Y : Over x, Flat ((toScheme B S hS p).map Y.hom) →
      (F.presheaf.obj (op Y.left) ≅ (quasiCoherentPresheafFunctor (p.obj x).left.1 d.val).obj
        (op ((Over.post (toScheme B S hS p)).obj Y))) := fun Y hY ↦
    liftedSectionsIso B E h S hS p hp F hlqc Y.hom d.val d.isQuasicoherent d.isSheaf d.iso
      (hbc Y.hom hY)
  have he : ∀ {Y Y' : Over x} (hY : Flat ((toScheme B S hS p).map Y.hom))
      (hY' : Flat ((toScheme B S hS p).map Y'.hom)) (g : Y' ⟶ Y),
      F.presheaf.map g.left.op ≫ (e Y' hY').hom =
        (e Y hY).hom ≫ (quasiCoherentPresheafFunctor (p.obj x).left.1 d.val).map
          ((Over.post (toScheme B S hS p)).map g).op := by
    intro Y Y' hY hY' g
    exact hcoc F hlqc d.val d.isQuasicoherent d.isSheaf d.iso g.left Y.hom Y'.hom
      (Over.w g).symm (hbc Y.hom hY) (hbc Y'.hom hY')
  exact isZero_cechCohomology_of_flatSectionsIso B S hS p hp F.presheaf d.val e he 𝒰 hstd n hn

end AlgebraicGeometry.Stack

end
