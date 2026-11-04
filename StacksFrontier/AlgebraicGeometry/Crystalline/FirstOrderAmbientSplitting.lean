module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AmbientSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.FirstOrderIdealSheaf

/-!
# The restriction of a module along the first-order universal thickening splits

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF], let `F` be a sheaf
of `𝒪_{X/S}`-modules and let `(U, T, δ)` be an object of `CRIS(X/S)` with first-order universal
thickening `(U, T', δ')` of [Stacks, Tag 07J2].

The ambient schemes `T` and `T'` have the same underlying topological space, and the three
morphisms `i : T ⟶ T'`, `p₀, p₁ : T' ⟶ T` are the identity on it; their comorphisms are the
projection and the two inclusions of the square-zero extension `𝒪_{T'} = 𝒪_T ⊕ Ω_{T/S,δ}`. So
`F_T` and `F_{T'}` are sheaves of modules over two sheaves of rings on one and the same Zariski
site, and the two restrictions of scalars between them compose to the identity, because
`p₀ ∘ i = id`.

With no hypothesis on `F` and none on the object, the restriction of scalars `p₀_* F_{T'}` of
`F_{T'}` along the inclusion `𝒪_T ⟶ 𝒪_{T'}` is the direct sum of `F_T` and of the kernel of
`F_{T'} ⟶ i_* F_T`,

`p₀_* F_{T'} ≅ ker(F_{T'} ⟶ i_* F_T) ⊞ F_T`,

split by `p₀^*` on one side and by `i^*` on the other.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.Thickening.ambientFMap`: the `f`-map `F_{T'} ⟶ g_* F_T`
  of [Stacks, Tag 07IQ], read between sheaves of modules on the ambient schemes. Its value on
  sections over an open `W` is the restriction map of `F` along the restriction of `g` over `W`.
* `Crystalline.GlobalCrystallineSituation.firstOrderAmbientProjMap` and
  `Crystalline.GlobalCrystallineSituation.firstOrderAmbientInclMap`: the two maps `i^*` and
  `p₀^*` of that `f`-map at `i` and at `p₀`.
* `Crystalline.GlobalCrystallineSituation.firstOrderAmbientKernel`: the kernel of
  `i^* : p₀_* F_{T'} ⟶ F_T`, a sheaf of `𝒪_T`-modules.
* `Crystalline.GlobalCrystallineSituation.firstOrderAmbientSplitting`: the splitting of the
  short complex `0 ⟶ ker ⟶ p₀_* F_{T'} ⟶ F_T ⟶ 0` given by `p₀^*`.
* `Crystalline.GlobalCrystallineSituation.firstOrderAmbientBiprodIso`: the direct sum
  decomposition `p₀_* F_{T'} ≅ ker(i^*) ⊞ F_T`.

## Main results

* `Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenMap_id`: the restriction of an
  identity of `CRIS(X/S)` over an open is an identity.
* `Crystalline.GlobalCrystallineSituation.restrictOpenMap_siteι_comp_siteP₀`: the restrictions
  of `i` and of `p₀` over an open of `T` compose to an identity.
* `Crystalline.GlobalCrystallineSituation.firstOrderAmbientInclMap_comp_projMap`: `i^*` is a
  retraction of `p₀^*`.
* `Crystalline.GlobalCrystallineSituation.exact_firstOrderAmbientShortComplex`: the short
  complex is exact.

## References

* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

namespace Thickening

variable {S : GlobalCrystallineSituation.{u}} {A B : Thickening S}

/-! ### The `f`-map on the ambient schemes -/

/-- The restriction of an identity of `CRIS(X/S)` over an open is an identity. -/
theorem restrictOpenMap_id (A : Thickening S) (W : A.thickening.target.scheme.Opens) :
    restrictOpenMap (𝟙 A) W = 𝟙 (A.restrictOpen W) :=
  (cancel_mono (A.restrictOpenHom W)).1 (by
    rw [restrictOpenMap_restrictOpenHom, Category.comp_id]
    exact (Category.id_comp _).symm)

variable (M : SheafOfModules.{u} (crystallineStructureSheaf S))

/-- The restriction `F_T` of a sheaf of `𝒪_{X/S}`-modules to the ambient scheme `T` of an
object, as an object of the category `T.Modules` of sheaves of `𝒪_T`-modules. -/
abbrev ambientSchemeModule (M : SheafOfModules.{u} (crystallineStructureSheaf S))
    (A : Thickening S) : A.thickening.target.scheme.Modules :=
  ambientModuleRestriction M A

/-- The `f`-map `F_{T'} ⟶ g_* F_T` of a sheaf of `𝒪_{X/S}`-modules along a morphism `g` of
`CRIS(X/S)`, read between sheaves of modules on the ambient schemes: the scalars are the
structure sheaves of `T` and `T'` and the pushforward is the pushforward of modules along the
morphism of schemes `T ⟶ T'`. -/
def ambientFMap (g : A ⟶ B) :
    ambientSchemeModule M B ⟶
      (Scheme.Modules.pushforward g.targetHom.hom).obj (ambientSchemeModule M A) :=
  (SheafOfModules.restrictScalars (ringRestrictionSheafStructureIso B).inv).map
      (moduleFMapSheaf M g) ≫
    (ambientSchemePushforwardIso g).hom.app (moduleRestrictionSheaf M A)

/-- The `f`-map on the ambient schemes is, over an open `W`, the restriction map of `F` along
the restriction of the morphism over `W`. -/
theorem ambientFMap_val_app (g : A ⟶ B) (W : (B.thickening.target.scheme.Opens)ᵒᵖ)
    (x : (ambientSchemeModule M B).val.obj W) :
    (ambientFMap M g).val.app W x = moduleSiteRestrict M (restrictOpenMap g W.unop) x := rfl

end Thickening

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The relation `p₀ ∘ i = id` over an open -/

/-- The restrictions of `i` and of `p₀` over an open of `T` compose to the identity. -/
theorem restrictOpenMap_siteι_comp_siteP₀ (A : Thickening S)
    (W : A.thickening.target.scheme.Opens) :
    Thickening.restrictOpenMap (firstOrderThickeningSiteι S A)
          ((firstOrderThickeningSiteP₀ S A).targetHom.hom ⁻¹ᵁ W) ≫
        Thickening.restrictOpenMap (firstOrderThickeningSiteP₀ S A) W =
      𝟙 (A.restrictOpen W) := by
  refine (cancel_mono (A.restrictOpenHom W)).1 ?_
  simp only [Category.assoc, Thickening.restrictOpenMap_restrictOpenHom,
    Thickening.restrictOpenMap_restrictOpenHom_assoc, firstOrderThickeningSiteι_comp_P₀,
    Category.comp_id]
  exact (Category.id_comp _).symm

variable (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (A : Thickening S)

/-! ### The two maps between `F_T` and `F_{T'}` -/

/-- The map `i^* : F_{T'} ⟶ i_* F_T`, the restriction along the diagonal `i : T ⟶ T'`, as a
morphism of sheaves of `𝒪_{T'}`-modules. -/
abbrev firstOrderAmbientProjMap :
    Thickening.ambientSchemeModule M (firstOrderThickeningObject S A) ⟶
      (Scheme.Modules.pushforward (firstOrderThickeningSiteι S A).targetHom.hom).obj
        (Thickening.ambientSchemeModule M A) :=
  Thickening.ambientFMap M (firstOrderThickeningSiteι S A)

/-- The map `p₀^* : F_T ⟶ p₀_* F_{T'}`, the restriction along `p₀ : T' ⟶ T`, as a morphism of
sheaves of `𝒪_T`-modules. -/
abbrev firstOrderAmbientInclMap :
    Thickening.ambientSchemeModule M A ⟶
      (Scheme.Modules.pushforward (firstOrderThickeningSiteP₀ S A).targetHom.hom).obj
        (Thickening.ambientSchemeModule M (firstOrderThickeningObject S A)) :=
  Thickening.ambientFMap M (firstOrderThickeningSiteP₀ S A)

/-- The map `i^*` read over the scalars of `T`: the restriction of scalars along `p₀` of
`Crystalline.GlobalCrystallineSituation.firstOrderAmbientProjMap`, a morphism of sheaves of
`𝒪_T`-modules `p₀_* F_{T'} ⟶ F_T`. -/
abbrev firstOrderAmbientProjMap₀ :
    (Scheme.Modules.pushforward (firstOrderThickeningSiteP₀ S A).targetHom.hom).obj
        (Thickening.ambientSchemeModule M (firstOrderThickeningObject S A)) ⟶
      Thickening.ambientSchemeModule M A :=
  (Scheme.Modules.pushforward (firstOrderThickeningSiteP₀ S A).targetHom.hom).map
    (firstOrderAmbientProjMap M A)

/-- The map `i^*` is a retraction of `p₀^*`. -/
theorem firstOrderAmbientInclMap_comp_projMap :
    firstOrderAmbientInclMap M A ≫ firstOrderAmbientProjMap₀ M A =
      𝟙 (Thickening.ambientSchemeModule M A) := by
  ext W x
  have key : ∀ y : M.val.obj (op (A.restrictOpen W)),
      moduleSiteRestrict M (Thickening.restrictOpenMap (firstOrderThickeningSiteι S A)
          ((firstOrderThickeningSiteP₀ S A).targetHom.hom ⁻¹ᵁ W))
        (moduleSiteRestrict M
          (Thickening.restrictOpenMap (firstOrderThickeningSiteP₀ S A) W) y) = y := by
    intro y
    rw [moduleSiteRestrict_comp, restrictOpenMap_siteι_comp_siteP₀]
    exact moduleSiteRestrict_id M (A.restrictOpen W) y
  exact key x

/-! ### The kernel and the splitting -/

/-- The kernel of `i^* : p₀_* F_{T'} ⟶ F_T`, as a sheaf of `𝒪_T`-modules on the ambient scheme
of the object. -/
abbrev firstOrderAmbientKernel : A.thickening.target.scheme.Modules :=
  kernel (firstOrderAmbientProjMap₀ M A)

/-- The short complex `0 ⟶ ker(i^*) ⟶ p₀_* F_{T'} ⟶ F_T ⟶ 0` of sheaves of `𝒪_T`-modules. -/
def firstOrderAmbientShortComplex : ShortComplex A.thickening.target.scheme.Modules :=
  ShortComplex.mk (kernel.ι (firstOrderAmbientProjMap₀ M A)) (firstOrderAmbientProjMap₀ M A)
    (kernel.condition _)

/-- The retraction `p₀_* F_{T'} ⟶ ker(i^*)` of the kernel inclusion, through which the
idempotent `1 - p₀^* ∘ i^*` factors. -/
def firstOrderAmbientRetraction :
    (Scheme.Modules.pushforward (firstOrderThickeningSiteP₀ S A).targetHom.hom).obj
        (Thickening.ambientSchemeModule M (firstOrderThickeningObject S A)) ⟶
      firstOrderAmbientKernel M A :=
  kernel.lift (firstOrderAmbientProjMap₀ M A)
    (𝟙 _ - firstOrderAmbientProjMap₀ M A ≫ firstOrderAmbientInclMap M A) (by
      rw [Preadditive.sub_comp, Category.id_comp, Category.assoc,
        firstOrderAmbientInclMap_comp_projMap, Category.comp_id, sub_self])

/-- The retraction followed by the kernel inclusion is the idempotent `1 - p₀^* ∘ i^*`. -/
@[reassoc (attr := simp)]
theorem firstOrderAmbientRetraction_ι :
    firstOrderAmbientRetraction M A ≫ kernel.ι (firstOrderAmbientProjMap₀ M A) =
      𝟙 _ - firstOrderAmbientProjMap₀ M A ≫ firstOrderAmbientInclMap M A :=
  kernel.lift_ι _ _ _

/-- The splitting of the short complex `0 ⟶ ker(i^*) ⟶ p₀_* F_{T'} ⟶ F_T ⟶ 0` by `p₀^*` and
the retraction `firstOrderAmbientRetraction`. -/
def firstOrderAmbientSplitting : (firstOrderAmbientShortComplex M A).Splitting where
  r := firstOrderAmbientRetraction M A
  s := firstOrderAmbientInclMap M A
  f_r := by
    change kernel.ι (firstOrderAmbientProjMap₀ M A) ≫ firstOrderAmbientRetraction M A = 𝟙 _
    refine (cancel_mono (kernel.ι (firstOrderAmbientProjMap₀ M A))).1 ?_
    rw [Category.assoc, firstOrderAmbientRetraction_ι, Category.id_comp, Preadditive.comp_sub,
      Category.comp_id, ← Category.assoc, kernel.condition, Limits.zero_comp, sub_zero]
  s_g := firstOrderAmbientInclMap_comp_projMap M A
  id := by
    change firstOrderAmbientRetraction M A ≫ kernel.ι (firstOrderAmbientProjMap₀ M A) +
        firstOrderAmbientProjMap₀ M A ≫ firstOrderAmbientInclMap M A = 𝟙 _
    rw [firstOrderAmbientRetraction_ι, sub_add_cancel]

/-- The decomposition `p₀_* F_{T'} ≅ ker(i^*) ⊞ F_T` of `p₀_* F_{T'}` as the direct sum of the
kernel of `i^*` and of `F_T`. -/
def firstOrderAmbientBiprodIso :
    (Scheme.Modules.pushforward (firstOrderThickeningSiteP₀ S A).targetHom.hom).obj
        (Thickening.ambientSchemeModule M (firstOrderThickeningObject S A)) ≅
      firstOrderAmbientKernel M A ⊞ Thickening.ambientSchemeModule M A :=
  (firstOrderAmbientSplitting M A).isoBinaryBiproduct

/-- The short complex `0 ⟶ ker(i^*) ⟶ p₀_* F_{T'} ⟶ F_T ⟶ 0` is exact. -/
theorem exact_firstOrderAmbientShortComplex :
    (firstOrderAmbientShortComplex M A).Exact :=
  (firstOrderAmbientSplitting M A).exact

/-- The map `p₀^*` is a split monomorphism. -/
theorem isSplitMono_firstOrderAmbientInclMap :
    IsSplitMono (firstOrderAmbientInclMap M A) :=
  ⟨⟨⟨firstOrderAmbientProjMap₀ M A, firstOrderAmbientInclMap_comp_projMap M A⟩⟩⟩

/-- The map `i^*`, read over the scalars of `T`, is a split epimorphism. -/
theorem isSplitEpi_firstOrderAmbientProjMap₀ :
    IsSplitEpi (firstOrderAmbientProjMap₀ M A) :=
  ⟨⟨⟨firstOrderAmbientInclMap M A, firstOrderAmbientInclMap_comp_projMap M A⟩⟩⟩

end Crystalline.GlobalCrystallineSituation

end

end
