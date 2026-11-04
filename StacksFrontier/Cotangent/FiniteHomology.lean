module

public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.TensorProduct.Finite
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteCotangentComplex
public import StacksFrontier.Cotangent.PolynomialResolution
public import StacksCore.Tactic.StacksAttribute

/-!
# Finiteness of the cohomology of the cotangent complex

Let `A` be a Noetherian ring and let `A → B` be of finite type. Then every cohomology module
`H^n(L_{B/A})` is a finite `B`-module.

The terms of the complex `L_{B/A}` of Tag 08PN are *never* finite: the degree `-n` term is
`B ⊗_{P_n} Ω[P_n⁄A]` for `P_n` the `n`-th term of the standard resolution, a polynomial algebra
on the underlying set of `P_{n-1}`. So the statement cannot be read off the standard resolution.
The source's argument replaces the resolution: by Tag 08PX a finite type algebra over a
Noetherian ring admits a resolution all of whose terms are polynomial algebras on *finitely
many* variables, and Tag 08PY computes the cohomology of `Lπ_!` on any resolution, so the
cohomology of `L_{B/A}` is the cohomology of a complex of finite `B`-modules.

## Main definitions

* `Stacks.moduleCatSMul`, `Stacks.functorSMul` and `Stacks.complexSMul`: multiplication by a
  scalar as an endomorphism of a module, of a functor valued in modules, and of a complex of
  modules.
* `CommAlgCat.smallPolynomialModuleSheafSMul`: multiplication by a scalar as an endomorphism of
  a presheaf of `B`-modules on the small model of the restricted site `C_{B/A}`, read as an
  abelian sheaf by `CommAlgCat.smallPolynomialModuleSheaf`.
* `CommAlgCat.smallResolutionMooreComplex`: the Moore complex of `ℱ(P_•, ε)` for a presheaf of
  `B`-modules `ℱ` and a bounded resolution `ε : P_• ⟶ B`, formed in `B`-modules.

## Main results

* `Stacks.linearEquivOfSMulEquivariant`: an additive isomorphism of `B`-modules commuting with
  multiplication by every scalar is `B`-linear. This is what carries finiteness across the
  abelian-group-level computation of `Lπ_!`.
* `Stacks.finite_homology`: over a Noetherian ring, a complex whose term in one degree is a
  finite module has finite homology in that degree.
* `CommAlgCat.smallResolutionLeftDerivedMooreHomologyIso`: for a presheaf of `B`-modules `ℱ` on
  the small model of the restricted site, the sections at the point of `L_nπ_!(ℱ)` are the
  degree `n` homology of the Moore complex of `ℱ(P_•, ε)`, with its `B`-module structure
  forgotten.
* `CommAlgCat.smallResolutionLeftDerivedMooreHomologyIso_smul`: that isomorphism carries the
  endomorphism induced by multiplication by `b` on `ℱ` to multiplication by `b` on the homology.
* `CommAlgCat.finite_homology_smallResolutionMooreComplex`: **Tag 08PY** for a bounded
  resolution, in the form available here.
* `CommAlgCat.mooreHomologyLinearEquiv`: two bounded resolutions of `B` over `A` admitting the
  same cardinal bound have `B`-linearly isomorphic Moore homology for a fixed presheaf of
  `B`-modules. This is the resolution independence the argument needs, and the previous result is
  what makes it `B`-linear rather than merely additive.
* `CommAlgCat.finite_homology_cotangentComplex`: **Tag 08PZ**.

## Implementation notes

**The seam at `forget₂`, and how it is closed.** The computation of `Lπ_!` available in this
library — `CommAlgCat.smallResolutionLeftDerivedLowerShriekNatIso`, read at the small model of
the footnote-restricted site of `StacksFrontier/Cotangent/ResolutionPointCriterionSmall.lean` — has
coefficients in `AddCommGrpCat.{u}`: the module-level derived lower shriek does not exist here.
So the comparison of two resolutions that it produces is an isomorphism of *abelian groups*, and
`Module.Finite` does not transport along one: `⨁_{n : ℕ} k` and `k[x]` are isomorphic as abelian
groups, the second is a finite `k[x]`-module and the first is not.

What closes the gap is that the `B`-module structure of the sheaf is itself a family of
endomorphisms of the sheaf. For `b : B`, multiplication by `b` is an endomorphism
`CommAlgCat.smallPolynomialModuleSheafSMul` of the abelian sheaf underlying a presheaf of
`B`-modules, because the transition maps are `B`-linear. The computation of `Lπ_!` is natural in
the sheaf, and the remaining steps of the comparison are a coherence isomorphism and the
homology-preservation isomorphism of `forget₂`, both natural in the complex; so the comparison
commutes with those endomorphisms
(`CommAlgCat.smallResolutionLeftDerivedMooreHomologyIso_smul`). An additive map between
`B`-modules commuting with multiplication by every scalar *is* `B`-linear, which is
`Stacks.linearEquivOfSMulEquivariant`. Hence the comparison of two resolutions is `B`-linear and
finiteness transports. No hypothesis stands in for anything unproved.

**Why two resolutions and not a direct comparison.** The comparison between the complexes
`Ω[P_•⁄A] ⊗_{P_•} B` attached to two different resolutions is Remark 08QI, proved in
`StacksFrontier/Cotangent/ResolutionIndependence.lean`; it is not what is used here, this file
predating it. The comparison used
here is obtained instead by evaluating the *same* functor `L_nπ_!` on the *same* sheaf through
two different resolutions, which is what Tag 08PT provides; it needs both resolutions to be
cosimplicial objects of one site, hence one common cardinal bound on their variables. The bound
used is `CommAlgCat.standardResolutionVarCardinal A B`, which is infinite, so the finite type
resolution of Tag 08PX fits under it.

**Tag 08PY's hypothesis.** The source asks that `ℱ(P, α)` be a finite `B`-module for every
object of `C_{B/A}`. That is more than the proof uses and is not available here: the site in
force is the footnote-restricted one, whose objects are polynomial algebras on up to `κ`
variables, and for `ℱ = i^*Ω_{𝒪/A}` the sections on such an object are not finite. The
hypothesis carried is the one the Moore complex sees, namely finiteness of the sections on the
terms of the resolution; for the resolution of Tag 08PX those terms are polynomial algebras on
finitely many variables, which is the case the source's hypothesis is about.

## References

* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08PX](https://stacks.math.columbia.edu/tag/08PX)
* [Stacks Project, Tag 08PY](https://stacks.math.columbia.edu/tag/08PY)
* [Stacks Project, Tag 08PZ](https://stacks.math.columbia.edu/tag/08PZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial

universe v u

namespace Stacks

/-! ### Multiplication by a scalar, as an endomorphism -/

section SMul

variable {B : Type u} [CommRing B]

/-- Multiplication by `b` on a module, as an endomorphism in `ModuleCat B`. -/
def moduleCatSMul (M : ModuleCat.{v} B) (b : B) : M ⟶ M :=
  ModuleCat.ofHom (LinearMap.lsmul B M b)

/-- Every morphism of `B`-modules commutes with multiplication by a scalar: that is exactly its
`B`-linearity. Consequently multiplication by `b` is natural in the module. -/
lemma moduleCatSMul_comm {M N : ModuleCat.{v} B} (f : M ⟶ N) (b : B) :
    moduleCatSMul M b ≫ f = f ≫ moduleCatSMul N b := by
  ext x
  simp [moduleCatSMul, ModuleCat.hom_comp]

/-- Multiplication by `b` on a functor valued in `B`-modules, as an endomorphism of it. -/
def functorSMul {C : Type*} [Category C] (X : C ⥤ ModuleCat.{v} B) (b : B) : X ⟶ X where
  app c := moduleCatSMul (X.obj c) b
  naturality _ _ f := (moduleCatSMul_comm (X.map f) b).symm

/-- Every natural transformation of functors valued in `B`-modules commutes with multiplication
by a scalar. -/
lemma functorSMul_comm {C : Type*} [Category C] {X Y : C ⥤ ModuleCat.{v} B} (α : X ⟶ Y) (b : B) :
    functorSMul X b ≫ α = α ≫ functorSMul Y b :=
  NatTrans.ext (funext fun c => moduleCatSMul_comm (α.app c) b)

/-- Multiplication by `b` on a complex of `B`-modules, as an endomorphism of it. -/
def complexSMul {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex (ModuleCat.{v} B) c)
    (b : B) : K ⟶ K where
  f i := moduleCatSMul (K.X i) b
  comm' i j _ := moduleCatSMul_comm (K.d i j) b

/-- The alternating face map complex of multiplication by `b` is multiplication by `b`. -/
lemma alternatingFaceMapComplex_map_functorSMul (X : SimplicialObject (ModuleCat.{v} B)) (b : B) :
    (alternatingFaceMapComplex (ModuleCat.{v} B)).map (functorSMul X b) =
      complexSMul ((alternatingFaceMapComplex (ModuleCat.{v} B)).obj X) b :=
  rfl

/-- The map induced on homology by multiplication by `b` is multiplication by `b`. -/
lemma homologyMap_complexSMul {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{v} B) c) (b : B) (i : ι) [K.HasHomology i] :
    HomologicalComplex.homologyMap (complexSMul K b) i = moduleCatSMul (K.homology i) b := by
  rw [← cancel_epi (K.homologyπ i), HomologicalComplex.homologyπ_naturality,
    ← cancel_mono (K.homologyι i)]
  simp only [complexSMul, Category.assoc, moduleCatSMul_comm (K.homologyι i),
    HomologicalComplex.homology_π_ι_assoc, HomologicalComplex.homology_π_ι,
    HomologicalComplex.cyclesMap_i_assoc]
  rw [moduleCatSMul_comm (K.pOpcycles i)]

/-- **An additive isomorphism of `B`-modules commuting with multiplication by every scalar is
`B`-linear.** This is what lets a comparison of `B`-modules produced at abelian coefficients
carry finiteness: the hypothesis `h` is equivariance for the `B`-action, and equivariance for
every `b` is `B`-linearity. -/
def linearEquivOfSMulEquivariant {M N : ModuleCat.{u} B}
    (φ : (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).obj M ≅
      (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).obj N)
    (h : ∀ b : B, (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).map (moduleCatSMul M b) ≫ φ.hom =
      φ.hom ≫ (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).map (moduleCatSMul N b)) :
    M ≃ₗ[B] N := by
  refine AddEquiv.toLinearEquiv
    { toFun := fun x => φ.hom.hom x
      invFun := fun y => φ.inv.hom y
      left_inv := fun _ => by simp
      right_inv := fun _ => by simp
      map_add' := fun x y => by simp } ?_
  intro b x
  simpa [moduleCatSMul] using congrArg (fun f => AddCommGrpCat.Hom.hom f x) (h b)

/-- **Over a Noetherian ring, homology in a degree where the complex is finite is finite.** The
cycles inject into the term, hence are finite because the term is Noetherian, and the homology is
a quotient of the cycles. -/
theorem finite_homology {ι : Type*} {c : ComplexShape ι} [IsNoetherianRing B]
    (K : HomologicalComplex (ModuleCat.{v} B) c) (i : ι) [K.HasHomology i]
    (h : Module.Finite B (K.X i)) : Module.Finite B (K.homology i) := by
  have : IsNoetherian B (K.X i) := inferInstance
  have : IsNoetherian B (K.cycles i) :=
    isNoetherian_of_injective (R := B) (S := B) (K.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  have : Module.Finite B (K.cycles i) := inferInstance
  exact Module.Finite.of_surjective (K.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

/-- A module that is zero is finite. -/
theorem finite_of_isZero (M : ModuleCat.{v} B) (h : IsZero M) : Module.Finite B M := by
  have hz : ∀ x : (M : Type v), x = 0 := fun x => by
    simpa using congrArg (fun f => ModuleCat.Hom.hom f x) (h.eq_of_src (𝟙 M) 0)
  exact Module.Finite.of_surjective (0 : B →ₗ[B] M) fun y => ⟨0, by rw [hz y]; simp⟩

end SMul

/-- Three commuting squares in a row compose to one. -/
lemma comp_square {C : Type*} [Category C] {X₀ X₁ X₂ X₃ : C} {f₀ : X₀ ⟶ X₀} {f₁ : X₁ ⟶ X₁}
    {f₂ : X₂ ⟶ X₂} {f₃ : X₃ ⟶ X₃} {a : X₀ ⟶ X₁} {b : X₁ ⟶ X₂} {c : X₂ ⟶ X₃}
    (h₁ : f₀ ≫ a = a ≫ f₁) (h₂ : f₁ ≫ b = b ≫ f₂) (h₃ : f₂ ≫ c = c ≫ f₃) :
    f₀ ≫ a ≫ b ≫ c = (a ≫ b ≫ c) ≫ f₃ := by
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]

/-! ### Naturality of the homology-preservation isomorphism -/

/-- `Stacks.mapHomologicalComplexHomologyIso` is natural in the complex. -/
lemma mapHomologicalComplexHomologyIso_hom_naturality {C₁ : Type*} [Category C₁] [Preadditive C₁]
    {C₂ : Type*} [Category C₂] [Preadditive C₂] {ι : Type*} {c : ComplexShape ι} (F : C₁ ⥤ C₂)
    [F.Additive] [F.PreservesHomology] {K L : HomologicalComplex C₁ c} (ψ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i]
    [((F.mapHomologicalComplex c).obj K).HasHomology i]
    [((F.mapHomologicalComplex c).obj L).HasHomology i] :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex c).map ψ) i ≫
        (mapHomologicalComplexHomologyIso F L i).hom =
      (mapHomologicalComplexHomologyIso F K i).hom ≫
        F.map (HomologicalComplex.homologyMap ψ i) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor C₁ c i).map ψ) F

end Stacks

namespace CommAlgCat

/-! ### Presheaves of modules on the small model of the restricted site -/

section Sheaf

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (κ : Cardinal.{u})
  (ℱ : (smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ ModuleCat.{u} B)

/-- Multiplication by `b` as an endomorphism of the abelian sheaf underlying a presheaf of
`B`-modules. It is a morphism of abelian sheaves because the transition maps of `ℱ` are
`B`-linear; this is the family of endomorphisms through which the `B`-module structure survives
the passage to abelian coefficients. -/
def smallPolynomialModuleSheafSMul (b : B) :
    smallPolynomialModuleSheaf A B κ ℱ ⟶ smallPolynomialModuleSheaf A B κ ℱ :=
  ⟨Functor.whiskerRight (Stacks.functorSMul ℱ b) (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u})⟩

/-- The underlying morphism of presheaves of `CommAlgCat.smallPolynomialModuleSheafSMul` is
multiplication by `b` on `ℱ`, with the module structures forgotten. -/
lemma sheafToPresheaf_map_smallPolynomialModuleSheafSMul (b : B) :
    (sheafToPresheaf (GrothendieckTopology.trivial (smallBoundedPolynomialSite A B κ))
          AddCommGrpCat.{u}).map (smallPolynomialModuleSheafSMul A B κ ℱ b) =
      Functor.whiskerRight (Stacks.functorSMul ℱ b)
        (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}) :=
  rfl

end Sheaf

/-! ### The Moore complex of a presheaf of modules on a bounded resolution -/

section Resolution

variable {A : Type u} [CommRing A] {B : CommAlgCat.{u} A}
  {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B) (κ : Cardinal.{u})
  (hPκ : ∀ n, IsPolynomialAlgebraBelow A κ (P.obj n))
  (ℱ : (smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ ModuleCat.{u} B)

/-- **The Moore complex of `ℱ(P_•, ε)`, formed in `B`-modules.** Here `ε : P_• ⟶ B` is a
resolution of `B` over `A` whose terms are polynomial algebras on at most `κ` variables and `ℱ`
is a presheaf of `B`-modules on the small model of the restricted site. -/
def smallResolutionMooreComplex : ChainComplex (ModuleCat.{u} B) ℕ :=
  (alternatingFaceMapComplex (ModuleCat.{u} B)).obj
    ((smallResolutionCosimplicialObject ε κ hPκ).op ⋙ ℱ)

variable (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A))))

/-- **`Lπ_!(ℱ) = ℱ(P_•, ε)` for a presheaf of `B`-modules, with the module structure forgotten.**
The sections at the point of `L_nπ_!(ℱ)` are the degree `n` homology of the `B`-module Moore
complex of `ℱ(P_•, ε)`, read as an abelian group.

This is `CommAlgCat.smallResolutionLeftDerivedLowerShriekNatIso` — the conclusion of Tag 08PT at
the small model of the restricted site — followed by the two identifications that move the
computation from abelian groups to `B`-modules: the Moore complex of the underlying abelian
presheaf is the image of the `B`-module Moore complex, and `forget₂` preserves homology. -/
@[stacks 08PY "the half of the statement that says which modules the conclusion is about: the \
  cohomology of Lπ_!(ℱ) for the point morphism of the small model of the footnote-restricted \
  site, read degreewise at abelian coefficients, is the homology of the B-module Moore complex \
  of ℱ(P_•, ε). The finiteness of those modules is \
  `CommAlgCat.finite_homology_smallResolutionMooreComplex`"]
def smallResolutionLeftDerivedMooreHomologyIso (n : ℕ) :
    (Stacks.ChaoticSite.pointSections.{u, u + 1, u} AddCommGrpCat.{u}).obj
        (((Stacks.ChaoticSite.abelianPointLowerShriek
              (smallBoundedPolynomialSite A B κ)).leftDerived n).obj
          (smallPolynomialModuleSheaf A B κ ℱ)) ≅
      (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).obj
        ((smallResolutionMooreComplex ε κ hPκ ℱ).homology n) :=
  (smallResolutionLeftDerivedLowerShriekNatIso ε κ hPκ hε n).app
      (smallPolynomialModuleSheaf A B κ ℱ) ≪≫
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n).mapIso
      ((alternatingFaceMapComplexCompMapHomologicalComplexIso
          (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u})).app
        ((smallResolutionCosimplicialObject ε κ hPκ).op ⋙ ℱ)).symm ≪≫
    Stacks.mapHomologicalComplexHomologyIso (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u})
      (smallResolutionMooreComplex ε κ hPκ ℱ) n

/-- **The computation of `Lπ_!` is compatible with multiplication by a scalar.** The endomorphism
of `L_nπ_!(ℱ)` induced by multiplication by `b` on `ℱ` corresponds, under
`CommAlgCat.smallResolutionLeftDerivedMooreHomologyIso`, to multiplication by `b` on the Moore
homology. Every step of that isomorphism is natural — in the sheaf for the first, in the
simplicial object for the second, in the complex for the third — and multiplication by `b` is a
morphism at each of those three places. -/
lemma smallResolutionLeftDerivedMooreHomologyIso_smul (n : ℕ) (b : B) :
    (Stacks.ChaoticSite.pointSections.{u, u + 1, u} AddCommGrpCat.{u}).map
          (((Stacks.ChaoticSite.abelianPointLowerShriek
                (smallBoundedPolynomialSite A B κ)).leftDerived n).map
            (smallPolynomialModuleSheafSMul A B κ ℱ b)) ≫
        (smallResolutionLeftDerivedMooreHomologyIso ε κ hPκ ℱ hε n).hom =
      (smallResolutionLeftDerivedMooreHomologyIso ε κ hPκ ℱ hε n).hom ≫
        (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).map
          (Stacks.moduleCatSMul ((smallResolutionMooreComplex ε κ hPκ ℱ).homology n) b) := by
  have hcoh := (alternatingFaceMapComplexCompMapHomologicalComplexIso
      (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u})).inv.naturality
    (Stacks.functorSMul ((smallResolutionCosimplicialObject ε κ hPκ).op ⋙ ℱ) b)
  have h₁ := (smallResolutionLeftDerivedLowerShriekNatIso ε κ hPκ hε n).hom.naturality
    (smallPolynomialModuleSheafSMul A B κ ℱ b)
  have h₂ := congrArg (HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
    (ComplexShape.down ℕ) n).map hcoh
  simp only [Functor.map_comp] at h₂
  have h₃ : (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n).map
          (((forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).mapHomologicalComplex
              (ComplexShape.down ℕ)).map
            (Stacks.complexSMul (smallResolutionMooreComplex ε κ hPκ ℱ) b)) ≫
        (Stacks.mapHomologicalComplexHomologyIso
          (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u})
          (smallResolutionMooreComplex ε κ hPκ ℱ) n).hom =
      (Stacks.mapHomologicalComplexHomologyIso (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u})
          (smallResolutionMooreComplex ε κ hPκ ℱ) n).hom ≫
        (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).map
          (Stacks.moduleCatSMul ((smallResolutionMooreComplex ε κ hPκ ℱ).homology n) b) := by
    rw [← Stacks.homologyMap_complexSMul]
    exact Stacks.mapHomologicalComplexHomologyIso_hom_naturality
      (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u})
      (Stacks.complexSMul (smallResolutionMooreComplex ε κ hPκ ℱ) b) n
  exact Stacks.comp_square h₁ h₂ h₃

/-- **Tag 08PY for a bounded resolution.** Let `B` be Noetherian, let `ε : P_• ⟶ B` be a
resolution of `B` over `A` whose terms are polynomial algebras on at most `κ` variables, and let
`ℱ` be a presheaf of `B`-modules on the small model of the restricted site whose sections on the
terms of the resolution are finite `B`-modules. Then the Moore homology of `ℱ(P_•, ε)` — which by
`CommAlgCat.smallResolutionLeftDerivedMooreHomologyIso` is the sections at the point of
`L_nπ_!(ℱ)` — is a finite `B`-module. -/
@[stacks 08PY "the conclusion for a resolution satisfying the cardinality bound of the small \
  model of the footnote-restricted site, and with the cohomology of Lπ_! read as the homology of \
  the B-module Moore complex of ℱ(P_•, ε), which is what identifies it here \
  (`CommAlgCat.smallResolutionLeftDerivedMooreHomologyIso`): the module-level Lπ_! is absent \
  from this library. The finiteness hypothesis is carried for the terms of the resolution, not \
  for every object of the site"]
theorem finite_homology_smallResolutionMooreComplex [IsNoetherianRing (B : Type u)]
    (hfin : ∀ p : SimplexCategory,
      Module.Finite B (ℱ.obj (op ((smallResolutionCosimplicialObject ε κ hPκ).obj p))))
    (n : ℕ) : Module.Finite B ((smallResolutionMooreComplex ε κ hPκ ℱ).homology n) :=
  Stacks.finite_homology _ n (hfin ⦋n⦌)

end Resolution

/-! ### Resolution independence of the Moore homology -/

section Comparison

variable {A : Type u} [CommRing A] {B : CommAlgCat.{u} A} (κ : Cardinal.{u})
  (ℱ : (smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ ModuleCat.{u} B)
  {P Q : SimplicialObject (CommAlgCat.{u} A)}
  (εP : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)
  (hPκ : ∀ n, IsPolynomialAlgebraBelow A κ (P.obj n))
  (hεP : SSet.trivialKanFibrations (Functor.whiskerRight εP (forget (CommAlgCat.{u} A))))
  (εQ : Q ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)
  (hQκ : ∀ n, IsPolynomialAlgebraBelow A κ (Q.obj n))
  (hεQ : SSet.trivialKanFibrations (Functor.whiskerRight εQ (forget (CommAlgCat.{u} A))))

/-- **The Moore homology of a presheaf of `B`-modules does not depend on the resolution, as a
`B`-module.** Two resolutions of `B` over `A` whose terms are polynomial algebras on at most `κ`
variables give `B`-linearly isomorphic Moore homology for a fixed presheaf of `B`-modules.

No comparison of the two resolutions is involved. Each computes the same functor `L_nπ_!` on the
same sheaf, by Tag 08PT at the small model of the restricted site; that identification is only
additive, and `B`-linearity comes from
`CommAlgCat.smallResolutionLeftDerivedMooreHomologyIso_smul`. -/
def mooreHomologyLinearEquiv (n : ℕ) :
    (smallResolutionMooreComplex εP κ hPκ ℱ).homology n ≃ₗ[(B : Type u)]
      (smallResolutionMooreComplex εQ κ hQκ ℱ).homology n := by
  refine Stacks.linearEquivOfSMulEquivariant
    ((smallResolutionLeftDerivedMooreHomologyIso εP κ hPκ ℱ hεP n).symm ≪≫
      smallResolutionLeftDerivedMooreHomologyIso εQ κ hQκ ℱ hεQ n) fun b => ?_
  have hP := smallResolutionLeftDerivedMooreHomologyIso_smul εP κ hPκ ℱ hεP n b
  have hQ := smallResolutionLeftDerivedMooreHomologyIso_smul εQ κ hQκ ℱ hεQ n b
  have hP' : (forget₂ (ModuleCat.{u} B) AddCommGrpCat.{u}).map
        (Stacks.moduleCatSMul ((smallResolutionMooreComplex εP κ hPκ ℱ).homology n) b) ≫
      (smallResolutionLeftDerivedMooreHomologyIso εP κ hPκ ℱ hεP n).inv =
      (smallResolutionLeftDerivedMooreHomologyIso εP κ hPκ ℱ hεP n).inv ≫
      (Stacks.ChaoticSite.pointSections.{u, u + 1, u} AddCommGrpCat.{u}).map
        (((Stacks.ChaoticSite.abelianPointLowerShriek
              (smallBoundedPolynomialSite A B κ)).leftDerived n).map
          (smallPolynomialModuleSheafSMul A B κ ℱ b)) := by
    rw [Iso.comp_inv_eq, Category.assoc, hP, Iso.inv_hom_id_assoc]
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, hP', Category.assoc, hQ, Category.assoc]

end Comparison

/-! ### Finiteness of the cohomology of the cotangent complex -/

section Finite

/-- The sections of `i^*Ω_{𝒪/A}` on an augmented algebra of essentially finite type over `A` are
a finite `B`-module: the differentials are finite over the algebra, and finiteness is preserved
by base change along the augmentation. -/
theorem finite_overDifferentials {A : Type u} [CommRing A] {B : CommAlgCat.{u} A} (X : Over B)
    [Algebra.EssFiniteType A (X.left : Type u)] : Module.Finite B (overDifferentials X) := by
  let _ : Algebra (X.left : Type u) (B : Type u) := (augmentationRingHom X).toAlgebra
  exact Module.Finite.base_change (X.left : Type u) (B : Type u)
    (KaehlerDifferential A (X.left : Type u))

/-- The cardinal bounding the variables of the standard resolution is infinite: the index types of
all the terms sit in its disjoint union, one copy for each degree. -/
theorem aleph0_le_standardResolutionVarCardinal (A : Type u) [CommRing A]
    (B : CommAlgCat.{u} A) : Cardinal.aleph0.{u} ≤ standardResolutionVarCardinal A B := by
  have : Infinite
      (Σ m : ℕ, (((polynomialComonad.{u, u} A).toFunctor.iterate m).obj B : Type u)) :=
    Infinite.of_injective (fun m => ⟨m, 0⟩) fun _ _ h => by
      simpa using congrArg Sigma.fst h
  exact Cardinal.infinite_iff.mp this

/-- A simplicial `A`-algebra whose terms are polynomial algebras on finitely many variables has
all its terms polynomial algebras on at most `κ` variables, for any infinite `κ`. This is what
puts the resolution of Tag 08PX and the standard resolution on the same site. -/
theorem isPolynomialAlgebraBelow_of_finiteType_terms {A : Type u} [CommRing A]
    {P : SimplicialObject (CommAlgCat.{u} A)} (κ : Cardinal.{u}) (hκ : Cardinal.aleph0.{u} ≤ κ)
    (hP : ∀ n : ℕ, ∃ k : ℕ, Nonempty ((P.obj (op ⦋n⦌) : Type u) ≃ₐ[A] MvPolynomial (Fin k) A))
    (p : SimplexCategoryᵒᵖ) : IsPolynomialAlgebraBelow A κ (P.obj p) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = op ⦋m⦌ := ⟨p.unop.len, by rw [SimplexCategory.mk_len]⟩
  obtain ⟨k, ⟨e⟩⟩ := hP m
  exact ⟨ULift.{u} (Fin k), le_of_lt (lt_of_lt_of_le Cardinal.mk_lt_aleph0 hκ),
    ⟨(MvPolynomial.renameEquiv A Equiv.ulift).trans e.symm⟩⟩

/-- The terms of a simplicial `A`-algebra that are polynomial algebras on finitely many variables
are of essentially finite type over `A`. -/
theorem essFiniteType_of_finiteType_terms {A : Type u} [CommRing A]
    {P : SimplicialObject (CommAlgCat.{u} A)}
    (hP : ∀ n : ℕ, ∃ k : ℕ, Nonempty ((P.obj (op ⦋n⦌) : Type u) ≃ₐ[A] MvPolynomial (Fin k) A))
    (p : SimplexCategoryᵒᵖ) : Algebra.EssFiniteType A (P.obj p : Type u) := by
  obtain ⟨m, rfl⟩ : ∃ m, p = op ⦋m⦌ := ⟨p.unop.len, by rw [SimplexCategory.mk_len]⟩
  obtain ⟨k, ⟨e⟩⟩ := hP m
  have : Algebra.FiniteType A (P.obj (op ⦋m⦌) : Type u) :=
    Algebra.FiniteType.equiv inferInstance e.symm
  infer_instance

/-- **The cohomology of `L_{B/A}` in degree `-n` is a finite `B`-module, given a resolution with
essentially finite type terms.** The hypotheses on `εQ` are exactly what Tag 08PX supplies for a
finite type algebra over a Noetherian ring: a resolution whose terms are polynomial algebras on
finitely many variables.

`CommAlgCat.mooreHomologyLinearEquiv` identifies the Moore homology of `i^*Ω_{𝒪/A}` on `εQ` and
on the standard resolution, `B`-linearly. On `εQ` the Moore complex has finite terms, so
Tag 08PY applies; on the standard resolution the Moore complex is the complex of `L_{B/A}`. -/
theorem finite_homology_cotangentComplex_of_resolution {A : Type u} [CommRing A]
    (B : CommAlgCat.{u} A) [IsNoetherianRing (B : Type u)]
    {Q : SimplicialObject (CommAlgCat.{u} A)}
    (εQ : Q ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)
    (hQκ : ∀ p, IsPolynomialAlgebraBelow A (standardResolutionVarCardinal A B) (Q.obj p))
    (hQfib : SSet.trivialKanFibrations (Functor.whiskerRight εQ (forget (CommAlgCat.{u} A))))
    (hQef : ∀ p : SimplexCategoryᵒᵖ, Algebra.EssFiniteType A (Q.obj p : Type u)) (n : ℕ) :
    Module.Finite B ((cotangentComplex.{u, u} A B).homology (-(n : ℤ))) := by
  have hfinQ : ∀ p : SimplexCategory, Module.Finite B
      ((smallPolynomialCotangentModulePresheaf A B (standardResolutionVarCardinal A B)).obj
        (op ((smallResolutionCosimplicialObject εQ (standardResolutionVarCardinal A B)
          hQκ).obj p))) := by
    intro p
    have hef : Algebra.EssFiniteType A (((resolutionOver εQ).obj (op p)).left : Type u) :=
      hQef (op p)
    have h1 : Module.Finite B
        ((resolutionOver εQ ⋙ overDifferentialsFunctor).obj (op p)) :=
      finite_overDifferentials _
    exact Module.Finite.equiv (((smallResolutionCotangentModuleIso εQ
      (standardResolutionVarCardinal A B) hQκ).app (op p)).symm.toLinearEquiv
        (R := (B : Type u)))
  have hQ := finite_homology_smallResolutionMooreComplex εQ
    (standardResolutionVarCardinal A B) hQκ
    (smallPolynomialCotangentModulePresheaf A B (standardResolutionVarCardinal A B)) hfinQ n
  have hstd : Module.Finite (B : Type u)
      ((smallResolutionMooreComplex (B := B) (standardResolution.{u, u} A B).hom
        (standardResolutionVarCardinal A B) (standardResolution_isPolynomialAlgebraBelow A B)
        (smallPolynomialCotangentModulePresheaf A B
          (standardResolutionVarCardinal A B))).homology n) := Module.Finite.equiv
    (mooreHomologyLinearEquiv (B := B) (standardResolutionVarCardinal A B)
      (smallPolynomialCotangentModulePresheaf A B (standardResolutionVarCardinal A B))
      (standardResolution.{u, u} A B).hom (standardResolution_isPolynomialAlgebraBelow A B)
      (standardResolution_isResolution.{u, u} A B).trivialKanFibration εQ hQκ hQfib n).symm
  exact hstd.equiv
    (((HomologicalComplex.homologyFunctor (ModuleCat.{u} B) (ComplexShape.down ℕ) n).mapIso
        ((alternatingFaceMapComplex (ModuleCat.{u} B)).mapIso
          (smallResolutionCotangentModuleIso (B := B) (standardResolution.{u, u} A B).hom
              (standardResolutionVarCardinal A B)
              (standardResolution_isPolynomialAlgebraBelow A B) ≪≫
            standardResolutionOverDifferentialsIso A B)) ≪≫
      (((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
            (cotangentSimplicialModule.{u, u} A B).object).extendHomologyIso
          (ComplexShape.embeddingUpIntLE 0) (j := n) (j' := -(n : ℤ))
          (by simp)).symm).toLinearEquiv (R := (B : Type u)))

/-- **Tag 08PZ.** Let `A` be a Noetherian ring and let `A → B` be a finite type ring map. Then
`H^n(L_{B/A})` is a finite `B`-module for every `n : ℤ`.

In positive degrees the cotangent complex vanishes, so there is nothing to prove; the content is
`CommAlgCat.finite_homology_cotangentComplex_of_resolution` fed with the finite type resolution
of Tag 08PX. -/
@[stacks 08PZ]
theorem finite_homology_cotangentComplex (A : Type u) [CommRing A] [IsNoetherianRing A]
    (B : Type u) [CommRing B] [Algebra A B] [Algebra.FiniteType A B] (m : ℤ) :
    Module.Finite B ((cotangentComplex.{u, u} A (CommAlgCat.of A B)).homology m) := by
  have _ : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  rcases le_or_gt m 0 with hm | hm
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = -(n : ℤ) := ⟨(-m).toNat, by omega⟩
    obtain ⟨Q, εQ, hQterms, hQfib⟩ :=
      exists_trivialKanFibration_from_finiteType_polynomial_simplicialAlgebra (A := A) (B := B)
    exact finite_homology_cotangentComplex_of_resolution (CommAlgCat.of A B) εQ
      (isPolynomialAlgebraBelow_of_finiteType_terms _
        (aleph0_le_standardResolutionVarCardinal A (CommAlgCat.of A B)) hQterms)
      hQfib (essFiniteType_of_finiteType_terms hQterms) n
  · exact Stacks.finite_homology _ m
      (Stacks.finite_of_isZero _ (cotangentComplex_isZero_pos.{u, u} A _ m hm))

end Finite

end CommAlgCat

end
