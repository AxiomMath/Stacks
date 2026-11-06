module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.IntersectionInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.CompletedLocalSpectrum
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.MinimalPrimesDirectLimit
public import StacksFrontier.AlgebraicGeometry.Stacks.FormalBranchComponents
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSite
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.StackComponentMultiplicity
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRingArtinApproximation
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRingFlatChartPoint
public import StacksFrontier.RingTheory.DiscreteValuationRing.SolutionCanonical
public import StacksFrontier.RingTheory.GRing.EssFiniteType
public import StacksFrontier.RingTheory.Length.RegularLocalHom
public import StacksFrontier.RingTheory.Length.RingEquiv

/-!
# Multiplicities of formal branches (Stacks 0DRD)

Let `𝒳` be an algebraic stack locally of finite type over a locally Noetherian scheme `S`, and let
`x₀ : Spec k ⟶ 𝒳` be a point with `k` of finite type over `S` and image `s ∈ S`. If `𝒪_{S,s}` is a
G-ring, the map of **Stacks 0DRB** from formal branches of `𝒳` through `x₀` to irreducible
components of `|𝒳|` through `x₀` preserves multiplicities (**Stacks 0DRC**, **Stacks 0DR8**).

The proof is the source's. By **Stacks 0DR0**, compatibly with the realization `Spec A ⟶ 𝒳`
(**Stacks 0DR1**, part (4)), there are a smooth chart `U ⟶ 𝒳` and a point `u₀` with
`𝒪^∧_{U,u₀} ≅ A`. The local ring `C = 𝒪_{U,u₀}` is essentially of finite type over `𝒪_{S,s}`,
hence a G-ring (**Stacks 07PV**), so `C → C^∧` is regular, and lengths of localizations at
minimal primes agree along it (`length_localization_comap_eq_of_isGRing`).

## Main results

* `AlgebraicGeometry.Scheme.exists_irreducibleComponents_fromSpecCompletedLocalRing_eq`: for a
  locally Noetherian scheme `X` and a point `x` whose local ring is a G-ring, every minimal prime
  `𝔭` of `𝒪^∧_{X,x}` maps under `Spec 𝒪^∧_{X,x} ⟶ X` to the generic point of an irreducible
  component `W` of `X` through `x`, and the local ring there has the length of `(𝒪^∧_{X,x})_𝔭`.
* `AlgebraicGeometry.Stack.componentMultiplicity_closure_chartPointMap_fromSpecCompletedLocalRing`:
  the same read on a smooth chart of a locally Noetherian stack.
* `AlgebraicGeometry.Stack.isGRing_stalk_of_schemeMap_eq`: the local ring of the chart of
  Stacks 0DR0 is a G-ring.
* `AlgebraicGeometry.Stack.componentMultiplicity_closure_basePointMap`: **Stacks 0DRD** at the
  value of the map of Stacks 0DRB.
* `AlgebraicGeometry.Stack.componentMultiplicity_formalBranchComponent`: **Stacks 0DRD**, the map
  `AlgebraicGeometry.Stack.formalBranchComponent` of Stacks 0DRB preserves multiplicities.

## References

* [Stacks Project, Tag 0DR0](https://stacks.math.columbia.edu/tag/0DR0)
* [Stacks Project, Tag 0DR8](https://stacks.math.columbia.edu/tag/0DR8)
* [Stacks Project, Tag 0DRB](https://stacks.math.columbia.edu/tag/0DRB)
* [Stacks Project, Tag 0DRC](https://stacks.math.columbia.edu/tag/0DRC)
* [Stacks Project, Tag 0DRD](https://stacks.math.columbia.edu/tag/0DRD)
* [Stacks Project, Tag 07PV](https://stacks.math.columbia.edu/tag/07PV)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace IsLocalRing

universe u w

namespace AlgebraicGeometry.Scheme

/-- **Formal branches of a scheme at a point with G-ring local ring.** Let `X` be a locally
Noetherian scheme and `x ∈ X` a point whose local ring `𝒪_{X,x}` is a G-ring. A minimal prime `𝔭`
of the completion `𝒪^∧_{X,x}` maps under `Spec 𝒪^∧_{X,x} ⟶ X` to the generic point of an
irreducible component `W` of `X` passing through `x`, and the local ring of `X` at that generic
point has the same length as `(𝒪^∧_{X,x})_𝔭`. The completion map `𝒪_{X,x} → 𝒪^∧_{X,x}` is
regular, so this is `length_localization_comap_eq_of_isGRing`. -/
theorem exists_irreducibleComponents_fromSpecCompletedLocalRing_eq (X : Scheme.{u})
    [IsLocallyNoetherian X] (x : X) (hG : IsGRing (X.presheaf.stalk x))
    (P : Ideal (X.completedLocalRing x)) (hP : P ∈ minimalPrimes (X.completedLocalRing x)) :
    ∃ W : irreducibleComponents X, x ∈ (W : Set X) ∧
      X.fromSpecCompletedLocalRing x ⟨P, hP.1.1⟩ = (genericPoints.ofComponent W : X) ∧
      Module.length (X.presheaf.stalk (genericPoints.ofComponent W : X))
          (X.presheaf.stalk (genericPoints.ofComponent W : X)) =
        letI : P.IsPrime := hP.1.1
        Module.length (Localization.AtPrime P) (Localization.AtPrime P) := by
  have : P.IsPrime := hP.1.1
  let C := X.presheaf.stalk x
  let f := algebraMap C (X.completedLocalRing x)
  have hq : P.comap f ∈ minimalPrimes C :=
    comap_mem_minimalPrimes_of_flat f (AdicCompletion.flat_of_isNoetherian _) hP
  let q : PrimeSpectrum C := ⟨P.comap f, hq.1.1⟩
  obtain ⟨W, hxW, hW⟩ := exists_irreducibleComponents_fromSpecStalk_eq x q hq
  refine ⟨W, hxW, (Scheme.Hom.comp_apply (Spec.map (X.toCompletedLocalRing x))
    (X.fromSpecStalk x) _).trans hW, ?_⟩
  rw [← hW]
  have : IsIso ((X.fromSpecStalk x).stalkMap q) := isIso_stalkMap_fromSpecStalk x q
  rw [Module.length_eq_of_ringEquiv
      (asIso ((X.fromSpecStalk x).stalkMap q)).commRingCatIsoToRingEquiv,
    ← length_localization_comap_eq_of_isGRing C hG P hP]
  exact Module.length_eq_of_ringEquiv (StructureSheaf.stalkIso C q).toRingEquiv.symm

/-- **Formal branches of a scheme through a presentation of the completed local ring.** Let `X`
be a locally Noetherian scheme, `x ∈ X` a point whose local ring is a G-ring, and
`e : 𝒪^∧_{X,x} ≅ A` a ring isomorphism. A minimal prime `𝔭` of `A` corresponds to the minimal
prime `e⁻¹ 𝔭` of `𝒪^∧_{X,x}`, which maps under `Spec 𝒪^∧_{X,x} ⟶ X` to the generic point of an
irreducible component `W` of `X` through `x`; the multiplicity of `W` (**Stacks 02QU**) is the
length of `A_𝔭`. -/
theorem exists_irreducibleComponents_componentMultiplicity_eq_of_ringEquiv (X : Scheme.{u})
    [IsLocallyNoetherian X] (x : X) (hG : IsGRing (X.presheaf.stalk x)) {A : Type u} [CommRing A]
    (e : X.completedLocalRing x ≃+* A) (P : Ideal A) (hP : P ∈ minimalPrimes A) :
    ∃ (hP' : P.comap (e : X.completedLocalRing x →+* A) ∈
        minimalPrimes (X.completedLocalRing x)) (W : irreducibleComponents X),
      x ∈ (W : Set X) ∧
      X.fromSpecCompletedLocalRing x ⟨P.comap (e : X.completedLocalRing x →+* A), hP'.1.1⟩ =
        (genericPoints.ofComponent W : X) ∧
      _root_.Stacks.Chow.componentMultiplicity (𝟙 X) (genericPoints.ofComponent W) =
        letI : P.IsPrime := hP.1.1
        ((Module.length (Localization.AtPrime P) (Localization.AtPrime P)).toNat : ℤ) := by
  have : P.IsPrime := hP.1.1
  have hP' : P.comap (e : X.completedLocalRing x →+* A) ∈ minimalPrimes (X.completedLocalRing x) :=
    comap_mem_minimalPrimes_of_flat _ (RingHom.Flat.of_bijective e.bijective) hP
  have : (P.comap (e : X.completedLocalRing x →+* A)).IsPrime := hP'.1.1
  obtain ⟨W, hxW, hW, hlen⟩ :=
    exists_irreducibleComponents_fromSpecCompletedLocalRing_eq X x hG _ hP'
  refine ⟨hP', W, hxW, hW, ?_⟩
  rw [_root_.Stacks.Chow.componentMultiplicity_eq_length_stalk, hlen,
    Module.length_eq_of_ringEquiv (localizationAtPrimeRingEquivOfRingEquiv e rfl)]

/-- **G-rings ascend along morphisms locally of finite type.** If `f : X ⟶ Y` is locally of finite
type and the local ring of `Y` at `f x` is a G-ring, so is the local ring of `X` at `x`: it is
essentially of finite type over it (**Stacks 07PV**). -/
theorem isGRing_stalk_of_locallyOfFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x : X) (hG : IsGRing (Y.presheaf.stalk (f x))) :
    IsGRing (X.presheaf.stalk x) := by
  let := (f.stalkMap x).hom.toAlgebra
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    LocallyOfFiniteType.stalkMap f x
  exact isGRing_of_essFiniteType hG

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Stack

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The multiplicity of the component of a stack through a formal branch of a smooth chart.**
Let `𝒳` be a locally Noetherian algebraic stack over `S`, let `x` be a smooth object of `𝒳`, lying
over a scheme `U`, let `u₀ ∈ U` be a point whose local ring is a G-ring and let
`e : 𝒪^∧_{U,u₀} ≅ A`. For a minimal prime `𝔭` of `A`, the closure of the image in `|𝒳|` of the
closure of the image of `e⁻¹ 𝔭` under `Spec 𝒪^∧_{U,u₀} ⟶ U` is an irreducible component of `|𝒳|`
(**Stacks 0DR5**), and its multiplicity (**Stacks 0DR8**) is the length of `A_𝔭`. -/
theorem componentMultiplicity_closure_chartPointMap_fromSpecCompletedLocalRing
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (hN : HasPropertyOnSomeSchemeAtlas B S hS
      (fun X : Scheme.{u} => IsLocallyNoetherian X) 𝒳)
    (x : 𝒳.val.val.obj) (hx : smoothObject.{u, w} B S hS 𝒳 x)
    (u₀ : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x))
    (hG : IsGRing (((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)).presheaf.stalk u₀))
    {A : Type u} [CommRing A]
    (e : ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)).completedLocalRing u₀ ≃+* A)
    (P : Ideal A) (hP : P ∈ minimalPrimes A)
    (hZ : closure (AlgebraicStacks.chartPointMap B S hS (𝒳.val.val.p.obj x) 𝒳
        (Bicategory.InducedBicategory.mkHom
          (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl))) ''
        closure {((BigFppfOver.toScheme B S hS).obj
                    (𝒳.val.val.p.obj x)).fromSpecCompletedLocalRing
                  u₀ ⟨P.comap e.toRingHom, hP.1.1.comap _⟩}) ∈
      irreducibleComponents (AlgebraicStacks.points B S hS 𝒳)) :
    componentMultiplicity.{u, w} B S hS 𝒳 hN _ hZ =
      letI : P.IsPrime := hP.1.1
      ((Module.length (Localization.AtPrime P) (Localization.AtPrime P)).toNat : ℤ) := by
  let : ObjectProperty.IsLocal (fun T : Scheme.{u} => IsLocallyNoetherian T)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)) :=
    (exists_scheme_atlas_iff_forall_scheme.{u, w} B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) 𝒳).mp hN _ _ hx
  obtain ⟨_, W, -, hW, hmult⟩ :=
    Scheme.exists_irreducibleComponents_componentMultiplicity_eq_of_ringEquiv _ u₀ hG e P hP
  have hcl : closure
      {((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)).fromSpecCompletedLocalRing
        u₀ ⟨P.comap e.toRingHom, hP.1.1.comap _⟩} = (W : Set _) := by
    have hW' : ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x)).fromSpecCompletedLocalRing
        u₀ ⟨P.comap e.toRingHom, hP.1.1.comap _⟩ = (genericPoints.ofComponent W : _) := hW
    rw [hW']
    exact genericPoints.isGenericPoint_ofComponent W
  rw [← hmult]
  exact componentMultiplicity_eq.{u, w} B S hS 𝒳 hN _ hZ _ _ hx W (by rw [hcl])

/-- **The local ring of the chart of Stacks 0DR0 is a G-ring.** In the versal situation, let `x₀`
lie over `Spec k ⟶ S` with image `s`, and let `x` be an object of `𝒳` over a scheme `U` locally of
finite type over `S`, with an arrow `x₀ ⟶ x` over `Spec k ≅ Spec κ(u₀) ⟶ U`. If `𝒪_{S,s}` is a
G-ring, then `u₀` lies over `s` and `𝒪_{U,u₀}` is a G-ring (**Stacks 07PV**). -/
theorem isGRing_stalk_of_schemeMap_eq (D : VersalSituation.{u, w})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (x : D.𝒳.val.val.obj) (u₀ : ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left)
    (e : k ≃+* ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.residueField u₀)
    (a : x₀ ⟶ x)
    (hlft : LocallyOfFiniteType ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).hom)
    (ha : Deformation.Artin.schemeMap (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) hx₀ rfl a =
        Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
          ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.fromSpecResidueField u₀)
    (s : D.S) (hs : (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) (closedPoint k) = s)
    (hG : IsGRing (D.S.presheaf.stalk s)) :
    IsGRing (((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.presheaf.stalk u₀) := by
  have hcomp := schemeMap_comp_hom
    (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) hx₀ rfl a
  rw [ha] at hcomp
  have h1 := congrArg (fun g => g.base (closedPoint k)) hcomp
  have hu : ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).hom u₀ = s := by
    rw [← hs]
    refine Eq.trans ?_ h1
    show _ = ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).hom
      (((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.fromSpecResidueField u₀ _)
    rw [Scheme.fromSpecResidueField_apply]
  subst hu
  exact Scheme.isGRing_stalk_of_locallyOfFiniteType _ u₀ hG

/-- **Stacks 0DRD, at the value of the map of Stacks 0DRB.** In the versal situation, let `x₀` lie
over `Spec k ⟶ S` with image `s` such that `𝒪_{S,s}` is a G-ring, let `ξ` be a versal formal object
of `x₀` over the versal ring `A` and let `y` over `Spec A` realize it. For a formal branch `𝔭` of
`𝒳` through `x₀`, if the closure of the image of `𝔭` in `|𝒳|` is an irreducible component (as
Stacks 0DRB shows), then its multiplicity (**Stacks 0DR8**) is the multiplicity of the branch
(**Stacks 0DRC**).

The proof is the source's: by **Stacks 0DR0**, compatibly with `y` (**Stacks 0DR1**, part (4)),
there is a smooth chart `U` with a point `u₀` and `𝒪^∧_{U,u₀} ≅ A`, along which `y` factors; the
local ring `𝒪_{U,u₀}` is a G-ring (**Stacks 07PV**) and the completion map is regular, so the
branch and the component of `U` it lies on have the same length. -/
theorem componentMultiplicity_closure_basePointMap (D : VersalSituation.{u, w})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (hξ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ)
    (s : D.S) (hs : (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) (closedPoint k) = s)
    (hG : IsGRing (D.S.presheaf.stalk s))
    {hA : D.B.Contains (Spec (.of ξ.base))} {y : D.𝒳.val.val.obj}
    {hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA}
    (Ry : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
      hfinite ξ).Realization hA y hy)
    {P : Ideal ξ.base} (hP : P ∈ formalBranches D iΛ hiΛ x₀ hx₀ hfinite ξ.base ⟨ξ, rfl, hξ⟩)
    (hZ : closure {AlgebraicStacks.basePointMap D.B D.S D.hS D.𝒳
                    (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA y hy
                    ⟨P, hP.1.1⟩} ∈
      irreducibleComponents (AlgebraicStacks.points D.B D.S D.hS D.𝒳)) :
    componentMultiplicity.{u, w} D.B D.S D.hS D.𝒳 D.hasLocallyNoetherianAtlas _ hZ =
      ((formalBranchMultiplicity D iΛ hiΛ x₀ hx₀ hfinite ξ.base ⟨ξ, rfl, hξ⟩ hP).toNat : ℤ) := by
  obtain ⟨x, u₀, e, a, eA, hlft, hsm, ha, m, hm⟩ :=
    exists_smoothObject_completedLocalRing_realization D iΛ hiΛ x₀ hx₀ hfinite ξ hξ s hs hG Ry
  have hGu := isGRing_stalk_of_schemeMap_eq D iΛ x₀ hx₀ x u₀ e a hlft ha s hs hG
  have hmor : (BigFppfOver.toScheme D.B D.S D.hS).map (eqToHom hy.symm ≫ D.𝒳.val.val.p.map m) =
      Spec.map (CommRingCat.ofHom eA.toRingHom) ≫
        ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.fromSpecCompletedLocalRing u₀ := by
    rw [← hm, Functor.map_comp, eqToHom_map]
    simp only [Deformation.Artin.schemeMap, eqToHom_refl, Category.comp_id]
    rfl
  have hcl := AlgebraicStacks.closure_basePointMap_eq_of_hom D.B D.S D.hS D.𝒳
    (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA hy m ⟨P, hP.1.1⟩
  have hpt : (BigFppfOver.toScheme D.B D.S D.hS).map (eqToHom hy.symm ≫ D.𝒳.val.val.p.map m)
      (AlgebraicStacks.baseOverPoint D.B D.S D.hS
        (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA ⟨P, hP.1.1⟩) =
      ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x).left.fromSpecCompletedLocalRing u₀
        ⟨P.comap eA.toRingHom, hP.1.1.comap _⟩ := by
    rw [hmor]
    rfl
  rw [hpt] at hcl
  have key : ∀ (T : Set (AlgebraicStacks.points D.B D.S D.hS D.𝒳))
      (hT : T ∈ irreducibleComponents (AlgebraicStacks.points D.B D.S D.hS D.𝒳)),
      T = closure (AlgebraicStacks.chartPointMap D.B D.S D.hS (D.𝒳.val.val.p.obj x) D.𝒳
        (Bicategory.InducedBicategory.mkHom
          (objectMorphism D.B D.S D.hS D.𝒳.val (Functor.Fiber.mk (a := x) rfl))) ''
        closure {((BigFppfOver.toScheme D.B D.S D.hS).obj
                    (D.𝒳.val.val.p.obj x)).fromSpecCompletedLocalRing u₀
                  ⟨P.comap eA.toRingHom, hP.1.1.comap _⟩}) →
      componentMultiplicity.{u, w} D.B D.S D.hS D.𝒳 D.hasLocallyNoetherianAtlas T hT =
        ((formalBranchMultiplicity D iΛ hiΛ x₀ hx₀ hfinite ξ.base ⟨ξ, rfl, hξ⟩ hP).toNat : ℤ) := by
    rintro T hT rfl
    exact componentMultiplicity_closure_chartPointMap_fromSpecCompletedLocalRing D.B D.S D.hS
      D.𝒳 D.hasLocallyNoetherianAtlas x hsm u₀ hGu eA P hP hT
  exact key _ hZ hcl

/-- **Stacks 0DRD.** Let `𝒳` be an algebraic stack locally of finite type over a locally
Noetherian scheme `S` (the versal situation, **Stacks 0DQU**) and let `x₀ : Spec k ⟶ 𝒳` be a point
with `k` a field of finite type over `S` and image `s ∈ S`. If `𝒪_{S,s}` is a G-ring, then the map
of **Stacks 0DRB**, from the formal branches of `𝒳` through `x₀` (read off the versal ring `A` of a
versal formal object `ξ` realized by `y` over `Spec A`) to the irreducible components of `|𝒳|`
through `x₀`, preserves multiplicities: the multiplicity (**Stacks 0DR8**) of the component
attached to a branch is the multiplicity of the branch (**Stacks 0DRC**). -/
@[stacks 0DRD]
theorem componentMultiplicity_formalBranchComponent (D : VersalSituation.{u, w})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (ξ : Deformation.FormalObject (Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀).projection)
    (hξ : Deformation.IsVersal (Deformation.Artin.predeformationCategory_isPredeformationCategory
      D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ)
    {hA : D.B.Contains (Spec (.of ξ.base))} {y : D.𝒳.val.val.obj}
    {hy : D.𝒳.val.val.p.obj y = Deformation.Artin.baseOver D.B D.S D.hS
      (Deformation.Artin.completeLocalAlgFormalBase iΛ hfinite ξ.base) hA}
    (Ry : (Deformation.Artin.FormalObject.ofPredeformation D.B D.S D.hS iΛ D.𝒳.val.val.p x₀ hx₀
      hfinite ξ).Realization hA y hy)
    (s : D.S) (hs : (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) (closedPoint k) = s)
    (hG : IsGRing (D.S.presheaf.stalk s))
    (P : formalBranches D iΛ hiΛ x₀ hx₀ hfinite ξ.base ⟨ξ, rfl, hξ⟩) :
    componentMultiplicity.{u, w} D.B D.S D.hS D.𝒳 D.hasLocallyNoetherianAtlas
        (formalBranchComponent D iΛ hiΛ x₀ hx₀ hfinite ξ hξ Ry P).1
        (formalBranchComponent D iΛ hiΛ x₀ hx₀ hfinite ξ hξ Ry P).2.1 =
      ((formalBranchMultiplicity D iΛ hiΛ x₀ hx₀ hfinite ξ.base ⟨ξ, rfl, hξ⟩ P.2).toNat : ℤ) :=
  componentMultiplicity_closure_basePointMap D iΛ hiΛ x₀ hx₀ hfinite ξ hξ s hs hG Ry P.2 _

end AlgebraicGeometry.Stack

end
