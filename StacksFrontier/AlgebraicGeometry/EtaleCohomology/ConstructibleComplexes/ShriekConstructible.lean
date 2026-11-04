module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekFiniteGeneration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Composition
import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero of a constructible sheaf of modules is constructible

Let `Λ` be a Noetherian ring and let `j : U ⟶ X` be an object of the small étale site of `X`
whose structure morphism is quasi-compact and quasi-separated. If `F` is a constructible sheaf of
`Λ`-modules on `U_étale` then `j_! F` is a constructible sheaf of `Λ`-modules on `X_étale`. This
is the general form of Stacks 03S8 for sheaves of modules: the statement already in the library,
`AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriekConstant`, is the case of the constant
free rank-one module sheaf.

The proof has two steps.

On a quasi-compact and quasi-separated `X` with `U` quasi-compact and quasi-separated as well, `F`
is presented as the cokernel of a map between two *finite* direct sums of the generators
`j_{W!}\underline{\Lambda}_W` at affine objects `W` of `U_étale`: the finite generation step of the
proof of Stacks 095N, `AlgebraicGeometry.exists_finite_epi_comp_sigma_moduleShriekConstant_affine`,
gives a finite surjection onto `F`, whose kernel is constructible because the constructible sheaves
of `Λ`-modules form a weak Serre subcategory (Stacks 03RZ (3)), and a second application of the
same statement presents that kernel. Extension by zero preserves cokernels and coproducts, being a
left adjoint, and it carries a generator to a generator — `j_{U!}j_{W!} = j_{(W∘U)!}`,
`AlgebraicGeometry.moduleExtensionByZeroCompIso` — so `j_! F` is the cokernel of a map between
finite direct sums of generators on `X_étale`, which are constructible by Stacks 03S8 for module
sheaves. The weak Serre property closes the class under that cokernel.

The quasi-compactness hypotheses are then removed by working on an affine open covering of `X`:
constructibility is Zariski local (Stacks 095F,
`AlgebraicGeometry.isConstructibleModuleSheaf_of_openCover`), extension by zero commutes with
base change (Stacks 03S6, `AlgebraicGeometry.moduleExtensionByZeroBaseChangeIso`), the base change
of `U` along an affine open `W ⟶ X` is quasi-compact and quasi-separated because the structure
morphism of `U` is, and the restriction of `F` to it stays constructible by Stacks 095G.

## Main results

* `AlgebraicGeometry.isConstructibleModuleSheaf_moduleExtensionByZero_of_compact` — the
  quasi-compact quasi-separated case.
* `AlgebraicGeometry.isConstructibleModuleSheaf_moduleExtensionByZero` — **extension by zero
  along a quasi-compact quasi-separated étale object carries constructible sheaves of
  `Λ`-modules to constructible sheaves of `Λ`-modules**, with no hypothesis on the ambient
  scheme.

## Implementation notes

No `@[stacks 03S8]` attribute is attached: the tag is registered on
`AlgebraicGeometry.isConstructibleSetSheaf_sheafifiedYoneda_of_qcqs` and
`AlgebraicGeometry.isConstructibleModuleSheaf_moduleShriekConstant`, which this statement is
proved *from*. It is the same convention as in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekBaseChange`.

The ring `Λ` lies in a universe `r` of its own and the sheaves of modules in
`ModuleCat.{max (u + 1) r} Λ`, the universe in which the coproducts defining the presheaf
extension by zero exist. Everything used is available there: Stacks 03S8 for module sheaves since
it is proved through `AlgebraicGeometry.moduleShriekConstantIsoCopower`, and the finite generation
step of Stacks 095N since it is in the general-ring section of its file.

The generators are written as `AlgebraicGeometry.moduleShriekConstant`, which is the extension by
zero of the constant sheaf with value the free rank-one module, so a generator on `U_étale` is
carried by `j_{U!}` to a generator on `X_étale` by the composition isomorphism applied to that
constant sheaf.

## References

* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
* [Stacks Project, Tag 095F](https://stacks.math.columbia.edu/tag/095F)
* [Stacks Project, Tag 095G](https://stacks.math.columbia.edu/tag/095G)
* [Stacks Project, Tag 03S6](https://stacks.math.columbia.edu/tag/03S6)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u r

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) r} Λ)]

/-- The constructible sheaves of `Λ`-modules on the small étale site of `X`, as a property of
objects of the category of sheaves of `Λ`-modules, at the coefficient universe of this file. -/
private abbrev constructibleModuleSheaves (X : B.Scheme) :
    ObjectProperty (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ)) :=
  fun F => IsConstructibleModuleSheaf B X Λ F

/-- The constructible sheaves of `Λ`-modules form a weak Serre subcategory: Stacks 03RZ (3). -/
private instance isWeakSerreClass_constructibleModuleSheaves (X : B.Scheme) :
    (constructibleModuleSheaves B Λ X).IsWeakSerreClass :=
  SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, r, r} B X Λ

/-- A weak Serre subcategory is closed under finite coproducts: a binary coproduct is a binary
biproduct, hence an extension of one summand by the other. -/
private instance isClosedUnderFiniteCoproducts_constructibleModuleSheaves (X : B.Scheme) :
    (constructibleModuleSheaves B Λ X).IsClosedUnderFiniteCoproducts := by
  have : (constructibleModuleSheaves B Λ X).IsClosedUnderBinaryCoproducts :=
    ObjectProperty.IsClosedUnderColimitsOfShape.mk' (fun _ ⟨H, hH⟩ =>
      (constructibleModuleSheaves B Λ X).prop_of_iso
        ((biprod.isoCoprod _ _).trans (HasColimit.isoOfNatIso (diagramIsoPair H)).symm)
        ((constructibleModuleSheaves B Λ X).prop_biprod (hH ⟨.left⟩) (hH ⟨.right⟩)))
  exact ObjectProperty.IsClosedUnderFiniteCoproducts.mk'

/-- **Extension by zero carries a generator to a generator.** The extension by zero along `U ⟶ X`
of the sheaf `j_{W!}\underline{\Lambda}_W` at an object `W` of the small étale site of `U` is the
sheaf `j_{(W∘U)!}\underline{\Lambda}` at the composite object of the small étale site of `X`:
both are the extension by zero of the same constant sheaf on `W`, along the two sides of
`AlgebraicGeometry.moduleExtensionByZeroCompIso`. -/
public def moduleExtensionByZeroObjModuleShriekConstantIso (X : B.Scheme)
    (U : SmallEtale B X.obj X.property)
    (W : SmallEtale B U.obj.left.obj U.obj.left.property) :
    (moduleExtensionByZero.{u, r} B X.obj X.property U Λ).obj
        (moduleShriekConstant.{u, r, r} B U.obj.left Λ W) ≅
      moduleShriekConstant.{u, r, r} B X Λ
        (smallEtaleCompObject B X.obj X.property U W) :=
  (moduleExtensionByZeroCompIso B X.obj X.property U W Λ).app
    ((constantSheaf (SmallEtale.topology B W.obj.left.obj W.obj.left.property)
      (ModuleCat.{max (u + 1) r} Λ)).obj (ModuleCat.of Λ (ULift.{max (u + 1) r} Λ)))

/-- **The extension by zero of a generator is constructible.** For `X` quasi-compact and
quasi-separated and `W` an affine object of the small étale site of `U`, the sheaf
`j_{U!}j_{W!}\underline{\Lambda}_W` is a constructible sheaf of `Λ`-modules on `X_étale`: it is
the generator at the composite object `W ⟶ U ⟶ X`, which is quasi-compact and quasi-separated
because `W` is affine, and Stacks 03S8 for sheaves of modules applies to it. -/
public theorem isConstructibleModuleSheaf_moduleExtensionByZero_moduleShriekConstant
    (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (U : SmallEtale B X.obj X.property)
    (W : SmallEtale B U.obj.left.obj U.obj.left.property)
    (hW : SmallEtale.IsAffine B U.obj.left.obj U.obj.left.property W) :
    IsConstructibleModuleSheaf B X Λ
      ((moduleExtensionByZero.{u, r} B X.obj X.property U Λ).obj
        (moduleShriekConstant.{u, r, r} B U.obj.left Λ W)) := by
  have hA : IsAffine ((SmallEtale.toScheme B U.obj.left.obj U.obj.left.property).obj W) := hW
  have hc : CompactSpace
      (smallEtaleCompObject B X.obj X.property U W).obj.left.obj :=
    inferInstanceAs
      (CompactSpace ((SmallEtale.toScheme B U.obj.left.obj U.obj.left.property).obj W))
  have hq : QuasiSeparatedSpace
      (smallEtaleCompObject B X.obj X.property U W).obj.left.obj :=
    inferInstanceAs
      (QuasiSeparatedSpace ((SmallEtale.toScheme B U.obj.left.obj U.obj.left.property).obj W))
  exact (constructibleModuleSheaves B Λ X).prop_of_iso
    (moduleExtensionByZeroObjModuleShriekConstantIso B Λ X U W).symm
    (isConstructibleModuleSheaf_moduleShriekConstant B X Λ
      (smallEtaleCompObject B X.obj X.property U W))

/-- **Stacks 03S8 for sheaves of modules, in its general form, on a quasi-compact quasi-separated
scheme.** Let `X` be a quasi-compact and quasi-separated scheme of a big étale site, let `U` be a
quasi-compact and quasi-separated object of its small étale site, and let `Λ` be a Noetherian
ring. The extension by zero of a constructible sheaf of `Λ`-modules on `U_étale` is a
constructible sheaf of `Λ`-modules on `X_étale`.

The sheaf is presented as the cokernel of a map between two finite direct sums of the generators
`j_{W!}\underline{\Lambda}_W` at affine objects of `U_étale`, by two applications of the finite
generation step of the proof of Stacks 095N; extension by zero preserves that cokernel and those
coproducts, being a left adjoint, and carries each generator to a constructible sheaf. -/
public theorem isConstructibleModuleSheaf_moduleExtensionByZero_of_compact
    (X : B.Scheme) [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (U : SmallEtale B X.obj X.property)
    [CompactSpace U.obj.left.obj] [QuasiSeparatedSpace U.obj.left.obj]
    (F : Sheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
      (ModuleCat.{max (u + 1) r} Λ))
    (hF : IsConstructibleModuleSheaf B U.obj.left Λ F) :
    IsConstructibleModuleSheaf B X Λ
      ((moduleExtensionByZero.{u, r} B X.obj X.property U Λ).obj F) := by
  set L := moduleExtensionByZero.{u, r} B X.obj X.property U Λ
  have : PreservesColimitsOfSize.{0, 0} L :=
    (moduleExtensionByZeroAdjunction B X.obj X.property U Λ).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits L := inferInstance
  obtain ⟨n, W, hW, p₀, hp₀⟩ :=
    exists_finite_epi_comp_sigma_moduleShriekConstant_affine B U.obj.left Λ (𝟙 F) hF
  have : Epi p₀ := by simpa using hp₀
  have hA₀ : IsConstructibleModuleSheaf B U.obj.left Λ
      (∐ fun i => moduleShriekConstant.{u, r, r} B U.obj.left Λ (W i)) :=
    isConstructibleModuleSheaf_sigma_moduleShriekConstant B U.obj.left Λ W hW
  have hK : IsConstructibleModuleSheaf B U.obj.left Λ (kernel p₀) :=
    (constructibleModuleSheaves B Λ U.obj.left).prop_kernel p₀ hA₀ hF
  obtain ⟨m, W', hW', p₁, hp₁⟩ :=
    exists_finite_epi_comp_sigma_moduleShriekConstant_affine B U.obj.left Λ
      (𝟙 (kernel p₀)) hK
  have : Epi p₁ := by simpa using hp₁
  have hzero : (p₁ ≫ kernel.ι p₀) ≫ p₀ = 0 := by
    rw [Category.assoc, kernel.condition, comp_zero]
  have hcolim : IsColimit (CokernelCofork.ofπ (f := p₁ ≫ kernel.ι p₀) p₀ hzero) :=
    isCokernelEpiComp (c := CokernelCofork.ofπ p₀ (kernel.condition p₀))
      (Abelian.epiIsCokernelOfKernel _ (limit.isLimit _)) p₁ rfl
  have eF : cokernel (p₁ ≫ kernel.ι p₀) ≅ F :=
    (colimit.isColimit _).coconePointUniqueUpToIso hcolim
  refine (constructibleModuleSheaves B Λ X).prop_of_iso (L.mapIso eF) ?_
  refine (constructibleModuleSheaves B Λ X).prop_of_iso
    (PreservesCokernel.iso L (p₁ ≫ kernel.ι p₀)).symm ?_
  have hsum : ∀ {k : ℕ} (V : Fin k → SmallEtale B U.obj.left.obj U.obj.left.property),
      (∀ i, SmallEtale.IsAffine B U.obj.left.obj U.obj.left.property (V i)) →
      IsConstructibleModuleSheaf B X Λ
        (L.obj (∐ fun i => moduleShriekConstant.{u, r, r} B U.obj.left Λ (V i))) :=
    fun V hV => (constructibleModuleSheaves B Λ X).prop_of_iso
      (PreservesCoproduct.iso L
        (fun i => moduleShriekConstant.{u, r, r} B U.obj.left Λ (V i))).symm
      ((constructibleModuleSheaves B Λ X).prop_coproduct fun i =>
        isConstructibleModuleSheaf_moduleExtensionByZero_moduleShriekConstant B Λ X U
          (V i) (hV i))
  exact (constructibleModuleSheaves B Λ X).prop_cokernel _ (hsum W' hW') (hsum W hW)

/-- **Stacks 03S8 for sheaves of modules, in its general form.** Let `Λ` be a Noetherian ring,
let `X` be a scheme of a big étale site and let `U` be an object of its small étale site whose
structure morphism is quasi-compact and quasi-separated. The extension by zero of a constructible
sheaf of `Λ`-modules on `U_étale` is a constructible sheaf of `Λ`-modules on `X_étale`. No
hypothesis on `X` is needed.

Constructibility is Zariski local, Stacks 095F, and on an affine open `Y` of `X` the restriction
of `j_! F` is `j_{U_Y!}` of the restriction of `F`, by Stacks 03S6; `Y` is quasi-compact and
quasi-separated, and so is `U_Y`, the structure morphism of `U` being quasi-compact and
quasi-separated, while the restriction of `F` stays constructible by Stacks 095G. -/
public theorem isConstructibleModuleSheaf_moduleExtensionByZero
    (X : B.Scheme) (U : SmallEtale B X.obj X.property)
    (hqc : QuasiCompact (B.inclusion.map U.obj.hom))
    (hqs : QuasiSeparated (B.inclusion.map U.obj.hom))
    (F : Sheaf (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
      (ModuleCat.{max (u + 1) r} Λ))
    (hF : IsConstructibleModuleSheaf B U.obj.left Λ F) :
    IsConstructibleModuleSheaf B X Λ
      ((moduleExtensionByZero.{u, r} B X.obj X.property U Λ).obj F) := by
  obtain ⟨I, Y, j, hj, hYaff, hcover⟩ := exists_affine_openCover_of_bigEtaleSite B X
  refine isConstructibleModuleSheaf_of_openCover B Λ X _ Y j hj hcover fun k => ?_
  have hA : IsAffine (Y k).obj := hYaff k
  have hYc : CompactSpace (Y k).obj := Scheme.compactSpace_of_isAffine _
  have hYq : QuasiSeparatedSpace (Y k).obj := quasiSeparatedSpace_of_isAffine _
  have hVqc : QuasiCompact
      (B.inclusion.map ((smallEtaleBaseChange B (j k)).obj U).obj.hom) :=
    MorphismProperty.of_isPullback (isPullback_smallEtaleBaseChange B (j k) U) hqc
  have hVqs : QuasiSeparated
      (B.inclusion.map ((smallEtaleBaseChange B (j k)).obj U).obj.hom) :=
    MorphismProperty.of_isPullback (isPullback_smallEtaleBaseChange B (j k) U) hqs
  have hYc' : CompactSpace (B.inclusion.obj (Y k)) := hYc
  have hYq' : QuasiSeparatedSpace (B.inclusion.obj (Y k)) := hYq
  have : CompactSpace ((smallEtaleBaseChange B (j k)).obj U).obj.left.obj :=
    @QuasiCompact.compactSpace_of_compactSpace _ _ _ hVqc hYc'
  have : QuasiSeparatedSpace ((smallEtaleBaseChange B (j k)).obj U).obj.left.obj :=
    @quasiSeparatedSpace_of_quasiSeparated _ _ _ hYq' hVqs
  have hpull := isConstructibleModuleSheaf_pullback B Λ
    (baseChangedEtaleProjection B (j k) U) F hF
  exact (constructibleModuleSheaves B Λ (Y k)).prop_of_iso
    ((moduleExtensionByZeroBaseChangeIso B (j k) U Λ).app F)
    (isConstructibleModuleSheaf_moduleExtensionByZero_of_compact B Λ (Y k)
      ((smallEtaleBaseChange B (j k)).obj U) _ hpull)

end AlgebraicGeometry

end

/-! ### Further declarations -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u r
attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts
namespace AlgebraicGeometry
variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) r} Λ)]

end AlgebraicGeometry
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u r
attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts
namespace AlgebraicGeometry
variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) r} Λ)]

end AlgebraicGeometry
end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u r
attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts
namespace AlgebraicGeometry
variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{max (u + 1) r} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{max (u + 1) r} Λ)]

end AlgebraicGeometry
end
