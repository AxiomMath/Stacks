module

public import StacksFrontier.Algebra.Category.ModuleCat.TensorBimodule
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.TensorInvertible
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.CechDegreewise
public import StacksFrontier.AlgebraicGeometry.SectionTensorFormula.AffineOpen

/-!
# The degreewise comparison for base change by a module

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square of schemes with `S` and `S'` affine, let `F` be a quasi-coherent
`𝒪_X`-module and let `G` be a quasi-coherent `𝒪_{S'}`-module. Write `A = Γ(S, ⊤)`,
`B = Γ(S', ⊤)` and `N = Γ(G, ⊤)`, a `B`-module and an `A`-module by restriction along `g`. The
coefficient module upstairs is

`F' = (f')^* G ⊗_{𝒪_{X'}} (g')^* F`,

and for every open `U` of `X` there is a canonical `B`-linear map

`N ⊗_A Γ(F, U) ⟶ Γ(F', (g')⁻¹U)`

sending `n ⊗ a` to the product of the pullback of `n` and the pullback of `a`. This file builds
that map, records its value on a pure tensor, and proves that it commutes with restriction along
an inclusion of opens.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleBaseChange.tensorPullback`: the coefficient module `F'`
  upstairs.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.coeffSection`: the pullback of a global section of
  `G` to a section of `(f')^* G` over an open of `X'`.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.comparisonSection`: the product of the pullback of a
  global section of `G` and the pullback of a section of `F`, a section of `F'`.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.comparisonMap`: **the comparison**
  `N ⊗_A Γ(F, U) ⟶ Γ(F', (g')⁻¹U)`, as a `B`-linear map.

## Main results

* `Stacks.AlgebraicGeometry.ModuleBaseChange.isQuasicoherent_tensorPullback`: `F'` is
  quasi-coherent.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.coeffSection_smul`: the pullback of a global section
  of `G` is semilinear along `f'`.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.comparisonSection_smul_base`: **the comparison is
  balanced over `A`** — the two ways of moving a scalar of `A` across the tensor sign agree,
  because the square commutes on sections.
* `Stacks.AlgebraicGeometry.ModuleBaseChange.comparisonMap_tmul`: **the normalisation.**
* `Stacks.AlgebraicGeometry.ModuleBaseChange.comparisonSection_res` and
  `Stacks.AlgebraicGeometry.ModuleBaseChange.comparisonMap_comm_res`: **the comparison commutes
  with restriction**, which is what turns the family of comparisons into a map of complexes.

## Implementation notes

The scalar structures over `A` and `B` are restrictions of scalars along the structure
morphisms, hence not instances; they are the ones of
`Stacks.AlgebraicGeometry.SectionsBaseChange.baseAlgebra` and
`Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule`, introduced by `letI` in the statements
exactly as in `StacksFrontier/AlgebraicGeometry/ProjectiveSpaceBaseChange/CechDegreewise.lean`.

The comparison is built as an additive map by `TensorProduct.liftAddHom` and upgraded to a
`B`-linear one by an induction over the tensor product, rather than by
`TensorProduct.AlgebraTensorModule.lift`. The reason is that the heterobasic lift asks for an
`A`-module structure on the target as well, and the target carries two of them — restriction
along `g' ≫ f` and along `f' ≫ g` — which are equal only by `IsPullback.w` and not
definitionally; the additive route never has to choose.

The balance over `A` is the one place the cartesian square is used, through
`Stacks.AlgebraicGeometry.SectionsBaseChange.sectionsSquare_comm` and
`Stacks.AlgebraicGeometry.SectionsBaseChange.appLE_comp_base`: a scalar of `A` pushed up through
`G` and then along `f'` is the same function on `X'` as the same scalar pushed along `f` and then
through `g'`.

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.SectionsBaseChange
open scoped TensorProduct

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory Stacks.SheafInternalHom.schemeMonoidalCategory

namespace Stacks.AlgebraicGeometry.ModuleBaseChange

variable {S S' X X' : Scheme.{u}}

/-! ### The coefficient module upstairs -/

/-- **The coefficient module upstairs**, `F' = (f')^* G ⊗ (g')^* F`. -/
abbrev tensorPullback (g' : X' ⟶ X) (f' : X' ⟶ S') (F : X.Modules) (G : S'.Modules) :
    X'.Modules :=
  (Scheme.Modules.pullback f').obj G ⊗ (Scheme.Modules.pullback g').obj F

/-- The pullback of a quasi-coherent module is quasi-coherent, [Stacks, Tag 01BG]. -/
instance isQuasicoherent_pullback' (g' : X' ⟶ X) (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pullback g').obj F).IsQuasicoherent :=
  AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback g' F

/-- **The coefficient module upstairs is quasi-coherent**: a pullback of a quasi-coherent module
is quasi-coherent ([Stacks, Tag 01BG]) and so is a tensor product of two ([Stacks, Tag 01CE]). -/
instance isQuasicoherent_tensorPullback (g' : X' ⟶ X) (f' : X' ⟶ S') (F : X.Modules)
    (G : S'.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (tensorPullback g' f' F G).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X'.ringCatSheaf).prop_of_iso
    (Stacks.SectionTensorFormula.tensorSheafIsoTensorObj X'.presheaf
      (Stacks.SectionTensorFormula.schemeSheafCondition X') _ _)
    (Scheme.Modules.isQuasicoherent_tensorObj _ _ inferInstance inferInstance)

/-- **The base scalar structures on the global sections of `G` form a tower.**  A scalar of
`Γ(S, ⊤)` acts through its image in `Γ(S', ⊤)`, which is the algebra map. -/
theorem coeffTower (g : S' ⟶ S) (G : S'.Modules) :
    letI := baseAlgebra g
    letI := baseModule g G ⊤
    IsScalarTower Γ(S, ⊤) Γ(S', ⊤) Γ(G, ⊤) :=
  let := baseAlgebra g
  let := baseModule g G ⊤
  Stacks.FlatSectionsDescent.isScalarTower_of_smul_eq (RingHom.id _) (fun _ _ => rfl)
    (g.appLE ⊤ ⊤ (le_preimage_top g ⊤)).hom (fun _ _ => rfl) (fun _ => rfl)

/-! ### The pullback of a global section of the coefficient module on the base -/

/-- **The pullback of a global section of `G`**, as a section of `(f')^* G` over an open `V` of
`X'`. -/
def coeffSection (f' : X' ⟶ S') (G : S'.Modules) (V : X'.Opens) (n : Γ(G, ⊤)) :
    Γ((Scheme.Modules.pullback f').obj G, V) :=
  pullbackSectionsHom f' G ⊤ V (le_preimage_top f' V) n

/-- The pullback of the zero global section of `G` is the zero section. -/
@[simp]
lemma coeffSection_zero (f' : X' ⟶ S') (G : S'.Modules) (V : X'.Opens) :
    coeffSection f' G V (0 : Γ(G, ⊤)) = 0 :=
  map_zero _

/-- The pullback of global sections of `G` is additive: it sends a sum to the sum of the
pullbacks. -/
lemma coeffSection_add (f' : X' ⟶ S') (G : S'.Modules) (V : X'.Opens) (n n' : Γ(G, ⊤)) :
    coeffSection f' G V (n + n') = coeffSection f' G V n + coeffSection f' G V n' :=
  map_add _ _ _

/-- **The pullback of a global section of `G` is semilinear along `f'`.** -/
lemma coeffSection_smul (f' : X' ⟶ S') (G : S'.Modules) (V : X'.Opens) (b : Γ(S', ⊤))
    (n : Γ(G, ⊤)) :
    coeffSection f' G V (b • n) =
      (f'.appLE ⊤ V (le_preimage_top f' V)).hom b • coeffSection f' G V n := by
  show (((Scheme.Modules.pullback f').obj G).presheaf.map
      (homOfLE (le_preimage_top f' V)).op).hom (pullbackUnitSections f' G ⊤ (b • n)) = _
  rw [pullbackUnitSections_smul f' G ⊤ b n,
    Scheme.Modules.map_smul ((Scheme.Modules.pullback f').obj G)
      (homOfLE (le_preimage_top f' V)) ((f'.app ⊤).hom b) (pullbackUnitSections f' G ⊤ n)]
  rfl

/-- **Restricting the pullback of a global section of `G`** gives the pullback over the smaller
open. -/
lemma coeffSection_res (f' : X' ⟶ S') (G : S'.Modules) {V W : X'.Opens} (h : W ≤ V)
    (n : Γ(G, ⊤)) :
    (((Scheme.Modules.pullback f').obj G).presheaf.map (homOfLE h).op).hom
        (coeffSection f' G V n) =
      coeffSection f' G W n := by
  show (((Scheme.Modules.pullback f').obj G).presheaf.map (homOfLE h).op).hom
      ((((Scheme.Modules.pullback f').obj G).presheaf.map
        (homOfLE (le_preimage_top f' V)).op).hom (pullbackUnitSections f' G ⊤ n)) = _
  rw [← ConcreteCategory.comp_apply,
    ← ((Scheme.Modules.pullback f').obj G).presheaf.map_comp]
  rfl

/-! ### The comparison on a pure tensor -/

variable (g' : X' ⟶ X) (f' : X' ⟶ S') (F : X.Modules) (G : S'.Modules)

/-- **The value of the comparison on a pure tensor**: the product of the pullback of a global
section of `G` and the pullback of a section of `F`. -/
def comparisonSection (U : X.Opens) (n : Γ(G, ⊤)) (a : Γ(F, U)) :
    Γ(tensorPullback g' f' F G, g' ⁻¹ᵁ U) :=
  Stacks.SectionTensorFormula.tensorSection _ _
    (coeffSection f' G (g' ⁻¹ᵁ U) n) (pullbackUnitSections g' F U a)

/-- The comparison on a pure tensor is additive in the global section of `G`. -/
lemma comparisonSection_add_left (U : X.Opens) (n n' : Γ(G, ⊤)) (a : Γ(F, U)) :
    comparisonSection g' f' F G U (n + n') a =
      comparisonSection g' f' F G U n a + comparisonSection g' f' F G U n' a := by
  rw [comparisonSection, coeffSection_add, Stacks.SectionTensorFormula.tensorSection_add_left]
  rfl

/-- The comparison on a pure tensor is additive in the section of `F` over `U`. -/
lemma comparisonSection_add_right (U : X.Opens) (n : Γ(G, ⊤)) (a a' : Γ(F, U)) :
    comparisonSection g' f' F G U n (a + a') =
      comparisonSection g' f' F G U n a + comparisonSection g' f' F G U n a' := by
  rw [comparisonSection, map_add, Stacks.SectionTensorFormula.tensorSection_add_right]
  rfl

/-- **The comparison is semilinear along `f'` in the coefficient variable.** -/
lemma comparisonSection_smul_coeff (U : X.Opens) (b : Γ(S', ⊤)) (n : Γ(G, ⊤)) (a : Γ(F, U)) :
    comparisonSection g' f' F G U (b • n) a =
      (f'.appLE ⊤ (g' ⁻¹ᵁ U) (le_preimage_top f' _)).hom b •
        comparisonSection g' f' F G U n a := by
  rw [comparisonSection, coeffSection_smul,
    Stacks.SectionTensorFormula.tensorSection_smul_left]
  rfl

/-- **The comparison is balanced over the base ring `A = Γ(S, ⊤)`.**  A scalar of `A` acting on
the global sections of `G` and then pushed up along `f'` is the same function on `(g')⁻¹U` as
the same scalar acting on the sections of `F` over `U` and then pushed up along `g'`; this is
the commutativity of the square read on sections. -/
lemma comparisonSection_smul_base {f : X ⟶ S} {g : S' ⟶ S} (H : IsPullback g' f' f g)
    (U : X.Opens) (α : Γ(S, ⊤)) (n : Γ(G, ⊤)) (a : Γ(F, U)) :
    letI := baseModule g G ⊤
    letI := baseModule f F U
    comparisonSection g' f' F G U (α • n) a =
      comparisonSection g' f' F G U n (α • a) := by
  let := baseModule g G ⊤
  let := baseModule f F U
  have hR : comparisonSection g' f' F G U n (α • a) =
      (g'.appLE U (g' ⁻¹ᵁ U) le_rfl).hom ((f.appLE ⊤ U (le_preimage_top f U)).hom α) •
        comparisonSection g' f' F G U n a := by
    show Stacks.SectionTensorFormula.tensorSection _ _ (coeffSection f' G (g' ⁻¹ᵁ U) n)
      (pullbackUnitSections g' F U ((f.appLE ⊤ U (le_preimage_top f U)).hom α • a)) = _
    rw [Scheme.Hom.appLE_preimage_self g' U,
      pullbackUnitSections_smul g' F U ((f.appLE ⊤ U (le_preimage_top f U)).hom α) a,
      Stacks.SectionTensorFormula.tensorSection_smul_right]
    rfl
  have hsq : (f'.appLE ⊤ (g' ⁻¹ᵁ U) (le_preimage_top f' _)).hom
        ((g.appLE ⊤ ⊤ (le_preimage_top g ⊤)).hom α) =
      (g'.appLE U (g' ⁻¹ᵁ U) le_rfl).hom ((f.appLE ⊤ U (le_preimage_top f U)).hom α) :=
    (sectionsSquare_comm H (g' ⁻¹ᵁ U) α).symm.trans (appLE_comp_base f g' U α)
  rw [hR, ← hsq]
  exact comparisonSection_smul_coeff g' f' F G U _ n a

/-- **The comparison commutes with restriction.**  Restricting the product of the two pullbacks
along the preimage of an inclusion of opens gives the product of the two pullbacks over the
smaller open. -/
lemma comparisonSection_res {U V : X.Opens} (h : V ≤ U) (n : Γ(G, ⊤)) (a : Γ(F, U)) :
    ((tensorPullback g' f' F G).presheaf.map
          (homOfLE (Scheme.Hom.preimage_mono g' h)).op).hom
        (comparisonSection g' f' F G U n a) =
      comparisonSection g' f' F G V n ((F.presheaf.map (homOfLE h).op).hom a) := by
  rw [comparisonSection,
    Stacks.SectionTensorFormula.map_tensorSection _ _
      (homOfLE (Scheme.Hom.preimage_mono g' h)) (coeffSection f' G (g' ⁻¹ᵁ U) n)
      (pullbackUnitSections g' F U a),
    coeffSection_res f' G (Scheme.Hom.preimage_mono g' h) n,
    ← pullbackUnitSections_naturality g' F h a]
  rfl

/-! ### The comparison -/

/-- The comparison `N ⊗_A Γ(F, U) ⟶ Γ(F', (g')⁻¹U)` as an additive map. -/
def comparisonAddHom {f : X ⟶ S} {g : S' ⟶ S} (H : IsPullback g' f' f g) (U : X.Opens) :
    letI := baseModule g G ⊤
    letI := baseModule f F U
    Γ(G, ⊤) ⊗[Γ(S, ⊤)] Γ(F, U) →+ Γ(tensorPullback g' f' F G, g' ⁻¹ᵁ U) :=
  letI := baseModule g G ⊤
  letI := baseModule f F U
  TensorProduct.liftAddHom
    (AddMonoidHom.mk'
      (fun n => AddMonoidHom.mk' (comparisonSection g' f' F G U n)
        (comparisonSection_add_right g' f' F G U n))
      (fun n n' => AddMonoidHom.ext (comparisonSection_add_left g' f' F G U n n')))
    (comparisonSection_smul_base g' f' F G H U)

/-- The additive comparison sends `n ⊗ a` to `comparisonSection g' f' F G U n a`. -/
@[simp]
lemma comparisonAddHom_tmul {f : X ⟶ S} {g : S' ⟶ S} (H : IsPullback g' f' f g) (U : X.Opens)
    (n : Γ(G, ⊤)) (a : Γ(F, U)) :
    letI := baseModule g G ⊤
    letI := baseModule f F U
    comparisonAddHom g' f' F G H U (n ⊗ₜ[Γ(S, ⊤)] a) = comparisonSection g' f' F G U n a :=
  rfl

/-- **The degreewise comparison.**  For an open `U` of `X` this is the `Γ(S', ⊤)`-linear map

`Γ(G, ⊤) ⊗_{Γ(S, ⊤)} Γ(F, U) ⟶ Γ((f')^* G ⊗ (g')^* F, (g')⁻¹U)`

sending `n ⊗ a` to the product of the pullback of `n` and the pullback of `a`. -/
def comparisonMap {f : X ⟶ S} {g : S' ⟶ S} (H : IsPullback g' f' f g) (U : X.Opens) :
    letI := baseModule g G ⊤
    letI := baseModule f F U
    letI := baseAlgebra g
    letI := coeffTower g G
    letI := baseModule f' (tensorPullback g' f' F G) (g' ⁻¹ᵁ U)
    Γ(G, ⊤) ⊗[Γ(S, ⊤)] Γ(F, U) →ₗ[Γ(S', ⊤)] Γ(tensorPullback g' f' F G, g' ⁻¹ᵁ U) :=
  letI := baseModule g G ⊤
  letI := baseModule f F U
  letI := baseAlgebra g
  letI := coeffTower g G
  letI := baseModule f' (tensorPullback g' f' F G) (g' ⁻¹ᵁ U)
  { toFun := comparisonAddHom g' f' F G H U
    map_add' := (comparisonAddHom g' f' F G H U).map_add
    map_smul' := by
      intro b z
      induction z using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | tmul n a => exact comparisonSection_smul_coeff g' f' F G U b n a
      | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add] }

/-- **The normalisation.**  The comparison sends `n ⊗ a` to the product of the pullback of the
global section `n` of `G` and the pullback of the section `a` of `F`. -/
@[simp]
lemma comparisonMap_tmul {f : X ⟶ S} {g : S' ⟶ S} (H : IsPullback g' f' f g) (U : X.Opens)
    (n : Γ(G, ⊤)) (a : Γ(F, U)) :
    letI := baseModule g G ⊤
    letI := baseModule f F U
    letI := baseAlgebra g
    letI := coeffTower g G
    letI := baseModule f' (tensorPullback g' f' F G) (g' ⁻¹ᵁ U)
    comparisonMap g' f' F G H U (n ⊗ₜ[Γ(S, ⊤)] a) = comparisonSection g' f' F G U n a :=
  rfl

/-- **The comparison commutes with restriction.**  Restricting after comparing over `U` is
comparing over `V` after restricting the second factor.  The Čech-style differential of a
hypercovering is an alternating sum of restrictions, so this is the compatibility that turns the
family of degreewise comparisons into a map of complexes. -/
theorem comparisonMap_comm_res {f : X ⟶ S} {g : S' ⟶ S} (H : IsPullback g' f' f g)
    {U V : X.Opens} (h : V ≤ U) :
    letI := baseModule g G ⊤
    letI := baseModule f F U
    letI := baseModule f F V
    letI := baseAlgebra g
    letI := coeffTower g G
    letI := baseModule f' (tensorPullback g' f' F G) (g' ⁻¹ᵁ U)
    letI := baseModule f' (tensorPullback g' f' F G) (g' ⁻¹ᵁ V)
    ∀ z : Γ(G, ⊤) ⊗[Γ(S, ⊤)] Γ(F, U),
      comparisonMap g' f' F G H V (LinearMap.lTensor Γ(G, ⊤) (baseResHom f F h) z) =
        ((tensorPullback g' f' F G).presheaf.map
            (homOfLE (Scheme.Hom.preimage_mono g' h)).op).hom
          (comparisonMap g' f' F G H U z) := by
  let := baseModule g G ⊤
  let := baseModule f F U
  let := baseModule f F V
  let := baseAlgebra g
  let := coeffTower g G
  let := baseModule f' (tensorPullback g' f' F G) (g' ⁻¹ᵁ U)
  let := baseModule f' (tensorPullback g' f' F G) (g' ⁻¹ᵁ V)
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact (map_zero _).symm
  | tmul n a => exact (comparisonSection_res g' f' F G h n a).symm
  | add x y hx hy =>
      rw [map_add, map_add, map_add, hx, hy]
      exact (map_add _ _ _).symm

end Stacks.AlgebraicGeometry.ModuleBaseChange

end
