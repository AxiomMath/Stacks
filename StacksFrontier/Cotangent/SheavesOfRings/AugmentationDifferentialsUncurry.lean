module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.FibreInclusion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModuleEquivalence
public import StacksFrontier.Cotangent.SheavesOfRings.SimplicialDerivationFibres

/-!
# `ε^*Ω_{𝒫/π^{-1}𝒜}` is the uncurrying of the base-changed simplicial differentials

Let `C` be a small site, let `f : 𝒜 ⟶ ℬ` be a homomorphism of sheaves of commutative rings on it
and let `P_• ⟶ ℬ` be the standard resolution of `ℬ` over `𝒜`, read on `Δ × C` as the sheaf of
commutative rings `𝒫` over `π^{-1}𝒜` with augmentation `ε : 𝒫 ⟶ π^{-1}ℬ`. This file proves

`ε^*Ω_{𝒫/π^{-1}𝒜} ≅ uncurryMod(Ω_{P_•/𝒜} ⊗_{P_•} ℬ)`

as sheaves of `π^{-1}ℬ`-modules on `Δ × C`, for *any* choice of the base-changed simplicial module
of [Stacks, Tag 08SS] — that is, for any `CategoryTheory.Sheaf.CotangentSimplicialModuleData`. Both
objects corepresent the functor `𝒩 ↦ Der_{π^{-1}𝒜}(𝒫, ε_*𝒩)`, with one and the same action of a
morphism `k : 𝒩 ⟶ 𝒩'` of coefficient modules, postcomposition with `ε_*k`.

## Main definitions

* `CategoryTheory.Sheaf.simplicialDifferentials`: `Ω_{𝒫/π^{-1}𝒜}` on `Δ × C`, the corepresenting
  object of the derivations functor there.
* `CategoryTheory.Sheaf.extendAugmentationScalars` and
  `CategoryTheory.Sheaf.extendAugmentationAdjunction`: `ε^*` and the adjunction `ε^* ⊣ ε_*` of
  [Stacks, Tag 03CZ] at the augmentation.
* `CategoryTheory.Sheaf.extendDifferentialsDerivationEquiv`:
  **`Hom(ε^*Ω_{𝒫/π^{-1}𝒜}, 𝒩) ≃ Der_{π^{-1}𝒜}(𝒫, ε_*𝒩)`.**
* `CategoryTheory.Sheaf.cotangentUncurryDerivationEquiv`:
  **`Hom(uncurryMod(D.object), 𝒩) ≃ Der_{π^{-1}𝒜}(𝒫, ε_*𝒩)`.**

## Main results

* `CategoryTheory.Sheaf.extendAugmentationDifferentialsUncurryIso`: **the two objects above are
  isomorphic**, both corepresenting the derivations of `𝒫` valued in `ε_*(-)`.

## References

* [Stacks Project, Tag 08SS](https://stacks.math.columbia.edu/tag/08SS), the base-changed
  simplicial module and the cotangent complex.
* [Stacks Project, Tag 09DH](https://stacks.math.columbia.edu/tag/09DH), the Atiyah triangle.
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ), extension of scalars.
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), the corepresentability of
  relative derivations.
* [Stacks Project, Tag 09D1](https://stacks.math.columbia.edu/tag/09D1), a simplicial module as a
  sheaf of modules on `Δ × C`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.SheafOfModules (derivationsFunctor)
open Stacks.Sheaves.RingedToposModules (commRingSheaf commRingSheafMap extendScalars
  extendRestrictScalarsAdjunction)
open Stacks.SimplicialModules (projection projectionTopology projectionRing projectionCommRing
  fibreRestrictionMod fibrewiseMod fibrewiseModMap uncurryMod simplicialModuleEquivalence
  isoOfHomEquivs)

universe u

namespace CategoryTheory.Sheaf

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [(projection C).IsCocontinuous (projectionTopology C J) J]
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  {A B : Sheaf J CommRingCat.{u}} (f : A ⟶ B)

/-- **`Ω_{𝒫/π^{-1}𝒜}`, the sheaf of relative differentials of the standard resolution on `Δ × C`**:
the object corepresenting the `π^{-1}𝒜`-derivations of `𝒫`. -/
abbrev simplicialDifferentials :
    SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (simplicialResolution J f)) :=
  (derivationsFunctor.{u} (simplicialBase J (A := A)) (simplicialResolution J f)
    (simplicialBaseMap J f)).coreprX

/-- **`ε^*`, extension of scalars along the augmentation** `ε : 𝒫 ⟶ π^{-1}ℬ` on `Δ × C`. -/
abbrev extendAugmentationScalars :
    SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (simplicialResolution J f)) ⥤
      SheafOfModules.{u} (projectionRing C J (targetRing J (B := B))) :=
  extendScalars (projectionTopology C J) (simplicialAugmentation J f).hom
    (Stacks.SheafOfModules.Tensor.ringSheaf (simplicialResolution J f)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf (projectionCommRing J B)).property

/-- **`ε^* ⊣ ε_*`**, the adjunction of [Stacks, Tag 03CZ] at the augmentation. -/
abbrev extendAugmentationAdjunction :
    extendAugmentationScalars J f ⊣
      SheafOfModules.restrictScalars (simplicialAugmentationRing J f) :=
  extendRestrictScalarsAdjunction (projectionTopology C J) (simplicialAugmentation J f).hom
    (Stacks.SheafOfModules.Tensor.ringSheaf (simplicialResolution J f)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf (projectionCommRing J B)).property

/-- **`Hom(ε^*Ω_{𝒫/π^{-1}𝒜}, 𝒩) ≃ Der_{π^{-1}𝒜}(𝒫, ε_*𝒩)`**: the adjunction `ε^* ⊣ ε_*` followed by
the corepresentation of the derivations functor. -/
def extendDifferentialsDerivationEquiv
    (N : SheafOfModules.{u} (projectionRing C J (targetRing J (B := B)))) :
    ((extendAugmentationScalars J f).obj (simplicialDifferentials J f) ⟶ N) ≃
      simplicialDerivations J f N :=
  ((extendAugmentationAdjunction J f).homEquiv (simplicialDifferentials J f) N).trans
    (derivationsFunctor.{u} (simplicialBase J (A := A)) (simplicialResolution J f)
      (simplicialBaseMap J f)).corepresentableBy.homEquiv

/-- The description is natural in the coefficient module: postcomposing a morphism with
`k : 𝒩 ⟶ 𝒩'` postcomposes the derivation with `ε_*k`. -/
theorem extendDifferentialsDerivationEquiv_naturality
    {N N' : SheafOfModules.{u} (projectionRing C J (targetRing J (B := B)))}
    (a : (extendAugmentationScalars J f).obj (simplicialDifferentials J f) ⟶ N) (k : N ⟶ N') :
    extendDifferentialsDerivationEquiv J f N' (a ≫ k) =
      (extendDifferentialsDerivationEquiv J f N a).postcomp
        ((SheafOfModules.restrictScalars (simplicialAugmentationRing J f)).map k).val := by
  have h1 : (extendAugmentationAdjunction J f).homEquiv (simplicialDifferentials J f) N'
        (a ≫ k) =
      (extendAugmentationAdjunction J f).homEquiv (simplicialDifferentials J f) N a ≫
        (SheafOfModules.restrictScalars (simplicialAugmentationRing J f)).map k :=
    Adjunction.homEquiv_naturality_right _ _ _
  exact ((congrArg (fun m => (derivationsFunctor.{u} (simplicialBase J (A := A))
      (simplicialResolution J f) (simplicialBaseMap J f)).corepresentableBy.homEquiv m) h1).trans
    ((derivationsFunctor.{u} (simplicialBase J (A := A)) (simplicialResolution J f)
      (simplicialBaseMap J f)).corepresentableBy.homEquiv_comp _ _))

/-- **`uncurryMod ⊣ fibrewiseMod`**, the adjunction of the equivalence
`Stacks.SimplicialModules.simplicialModuleEquivalence` read in the uncurrying direction. -/
abbrev simplicialUncurryAdjunction :
    uncurryMod C J (targetRing J (B := B)) ⊣ fibrewiseMod C J (targetRing J (B := B)) :=
  (simplicialModuleEquivalence C J (targetRing J (B := B))).symm.toAdjunction

/-! ### The uncurried side -/

variable {J f}

/-- The derivation attached to a composite is the derivation of the first factor, postcomposed on
sections with the second. This is the `naturality` field of the cotangent data, read on sections.
-/
theorem derivationEquiv_comp_d (D : CotangentSimplicialModuleData J f) (n : SimplexCategoryᵒᵖ)
    {M M' : targetModules J B} (g : D.object.obj n ⟶ M) (k : M ⟶ M') (U : Cᵒᵖ)
    (x : ((resolutionCommRing J f).obj n).obj.obj U) :
    (D.derivationEquiv n M' (g ≫ k)).d x = k.val.app U ((D.derivationEquiv n M g).d x) :=
  PresheafOfModules.Derivation.congr_d (D.naturality n g k) x

/-- **The family of degreewise derivations of a morphism into the fibrewise reading is
compatible**, in the sense of `CategoryTheory.Sheaf.simplicialDerivationOfFamily`. -/
theorem derivationEquiv_app_naturality (D : CotangentSimplicialModuleData J f)
    {N : SheafOfModules.{u} (projectionRing C J (targetRing J (B := B)))}
    (τ : D.object ⟶ (fibrewiseMod C J (targetRing J (B := B))).obj N)
    {m n : SimplexCategoryᵒᵖ} (α : m ⟶ n) (U : Cᵒᵖ)
    (x : ((resolutionCommRing J f).obj m).obj.obj U) :
    (D.derivationEquiv n (((fibrewiseMod C J (targetRing J (B := B))).obj N).obj n)
          (τ.app n)).d ((((resolutionCommRing J f).map α).hom.app U) x) =
      ((fibrewiseModMap C J (targetRing J (B := B)) α).app N).val.app U
        ((D.derivationEquiv m (((fibrewiseMod C J (targetRing J (B := B))).obj N).obj m)
          (τ.app m)).d x) :=
  ((D.simplex_naturality α (((fibrewiseMod C J (targetRing J (B := B))).obj N).obj n)
        (τ.app n) U x).symm.trans
      (PresheafOfModules.Derivation.congr_d
        (congrArg (fun g => D.derivationEquiv m
          (((fibrewiseMod C J (targetRing J (B := B))).obj N).obj n) g) (τ.naturality α)) x)).trans
    (derivationEquiv_comp_d D m (τ.app m)
      (((fibrewiseMod C J (targetRing J (B := B))).obj N).map α) U x)

/-- The degree-`n` transpose of a derivation of `𝒫` on `Δ × C`: the morphism out of the degree-`n`
term of the cotangent data matching the degree-`n` member of the family of derivations. -/
def cotangentFibreApp (D : CotangentSimplicialModuleData J f)
    {N : SheafOfModules.{u} (projectionRing C J (targetRing J (B := B)))}
    (d : simplicialDerivations J f N) (n : SimplexCategoryᵒᵖ) :
    D.object.obj n ⟶ ((fibrewiseMod C J (targetRing J (B := B))).obj N).obj n :=
  (D.derivationEquiv n _).symm (simplicialDerivationFibre n d)

/-- The degree-`n` derivation of the degree-`n` transpose of a derivation `d` is the degree-`n`
member of the family of `d`. -/
theorem derivationEquiv_cotangentFibreApp (D : CotangentSimplicialModuleData J f)
    {N : SheafOfModules.{u} (projectionRing C J (targetRing J (B := B)))}
    (d : simplicialDerivations J f N) (n : SimplexCategoryᵒᵖ) :
    D.derivationEquiv n (((fibrewiseMod C J (targetRing J (B := B))).obj N).obj n)
        (cotangentFibreApp D d n) =
      simplicialDerivationFibre n d :=
  (D.derivationEquiv n _).apply_symm_apply _

/-- **The morphism of simplicial sheaves of `ℬ`-modules attached to a derivation of `𝒫` on
`Δ × C`.** -/
def cotangentFibreMorphism (D : CotangentSimplicialModuleData J f)
    {N : SheafOfModules.{u} (projectionRing C J (targetRing J (B := B)))}
    (d : simplicialDerivations J f N) :
    D.object ⟶ (fibrewiseMod C J (targetRing J (B := B))).obj N where
  app n := cotangentFibreApp D d n
  naturality m n α :=
    (D.derivationEquiv m
        (((fibrewiseMod C J (targetRing J (B := B))).obj N).obj n)).injective
      (PresheafOfModules.Derivation.ext (funext fun U => AddMonoidHom.ext fun x =>
        ((D.simplex_naturality α (((fibrewiseMod C J (targetRing J (B := B))).obj N).obj n)
              (cotangentFibreApp D d n) U x).trans
            ((PresheafOfModules.Derivation.congr_d
                (derivationEquiv_cotangentFibreApp D d n) _).trans
              (simplicialDerivationFibre_naturality d α U x))).trans
          (((congrArg (fun y => ((fibrewiseModMap C J (targetRing J (B := B)) α).app N).val.app U y)
              (PresheafOfModules.Derivation.congr_d
                (derivationEquiv_cotangentFibreApp D d m) x)).symm).trans
            (derivationEquiv_comp_d D m (cotangentFibreApp D d m)
              (((fibrewiseMod C J (targetRing J (B := B))).obj N).map α) U x).symm)))

/-- **`Hom(uncurryMod(D.object), 𝒩) ≃ Der_{π^{-1}𝒜}(𝒫, ε_*𝒩)`**: the adjunction of the equivalence
`Stacks.SimplicialModules.simplicialModuleEquivalence`, followed by the degreewise corepresentation
of the derivations of the standard resolution and the identification of a derivation on `Δ × C`
with a compatible family. -/
def cotangentUncurryDerivationEquiv (D : CotangentSimplicialModuleData J f)
    (N : SheafOfModules.{u} (projectionRing C J (targetRing J (B := B)))) :
    ((uncurryMod C J (targetRing J (B := B))).obj D.object ⟶ N) ≃
      simplicialDerivations J f N where
  toFun g := simplicialDerivationOfFamily
    (fun n => D.derivationEquiv n (((fibrewiseMod C J (targetRing J (B := B))).obj N).obj n)
      (((simplicialUncurryAdjunction J (B := B)).homEquiv D.object N g).app n))
    (fun α U x => derivationEquiv_app_naturality D _ α U x)
  invFun d := ((simplicialUncurryAdjunction J (B := B)).homEquiv D.object N).symm
    (cotangentFibreMorphism D d)
  left_inv g :=
    (congrArg (fun τ => ((simplicialUncurryAdjunction J (B := B)).homEquiv D.object N).symm τ)
      (NatTrans.ext (funext fun n =>
        (D.derivationEquiv n (((fibrewiseMod C J (targetRing J (B := B))).obj N).obj n)
          ).symm_apply_apply
            (((simplicialUncurryAdjunction J (B := B)).homEquiv D.object N g).app n)))).trans
      (((simplicialUncurryAdjunction J (B := B)).homEquiv D.object N).symm_apply_apply g)
  right_inv d :=
    PresheafOfModules.Derivation.ext (funext fun X => AddMonoidHom.ext fun x =>
      PresheafOfModules.Derivation.congr_d
        ((congrArg (fun τ : D.object ⟶ (fibrewiseMod C J (targetRing J (B := B))).obj N =>
            D.derivationEquiv (op X.unop.1)
              (((fibrewiseMod C J (targetRing J (B := B))).obj N).obj (op X.unop.1))
              (τ.app (op X.unop.1)))
          (((simplicialUncurryAdjunction J (B := B)).homEquiv D.object N).apply_symm_apply
            (cotangentFibreMorphism D d))).trans
          (derivationEquiv_cotangentFibreApp D d (op X.unop.1))) x)

/-- The derivation a morphism out of the uncurrying gives, read on sections over `(n, U)`, is the
degree-`n` derivation of the corresponding morphism of simplicial objects. -/
theorem cotangentUncurryDerivationEquiv_d (D : CotangentSimplicialModuleData J f)
    (N : SheafOfModules.{u} (projectionRing C J (targetRing J (B := B))))
    (g : (uncurryMod C J (targetRing J (B := B))).obj D.object ⟶ N)
    (X : (SimplexCategory × C)ᵒᵖ) (x : ((simplicialResolution J f)).obj.obj X) :
    (cotangentUncurryDerivationEquiv D N g).d x =
      (D.derivationEquiv (op X.unop.1)
          (((fibrewiseMod C J (targetRing J (B := B))).obj N).obj (op X.unop.1))
          (((simplicialUncurryAdjunction J (B := B)).homEquiv D.object N g).app
            (op X.unop.1))).d (X := op X.unop.2) x :=
  rfl

/-- Postcomposing a derivation on `Δ × C` with `ε_*k` acts on sections as `k`. -/
theorem postcomp_restrictScalars_d
    {N N' : SheafOfModules.{u} (projectionRing C J (targetRing J (B := B)))}
    (d : simplicialDerivations J f N) (k : N ⟶ N') (X : (SimplexCategory × C)ᵒᵖ)
    (x : ((simplicialResolution J f)).obj.obj X) :
    (d.postcomp
        ((SheafOfModules.restrictScalars (simplicialAugmentationRing J f)).map k).val).d x =
      (((fibrewiseMod C J (targetRing J (B := B))).map k).app (op X.unop.1)).val.app
        (op X.unop.2) (d.d x) :=
  rfl

/-- The second description is natural in the coefficient module, with the same action as the first.
-/
theorem cotangentUncurryDerivationEquiv_naturality (D : CotangentSimplicialModuleData J f)
    {N N' : SheafOfModules.{u} (projectionRing C J (targetRing J (B := B)))}
    (b : (uncurryMod C J (targetRing J (B := B))).obj D.object ⟶ N) (k : N ⟶ N') :
    cotangentUncurryDerivationEquiv D N' (b ≫ k) =
      (cotangentUncurryDerivationEquiv D N b).postcomp
        ((SheafOfModules.restrictScalars (simplicialAugmentationRing J f)).map k).val := by
  refine PresheafOfModules.Derivation.ext (funext fun X => AddMonoidHom.ext fun x => ?_)
  rw [cotangentUncurryDerivationEquiv_d, postcomp_restrictScalars_d,
    Adjunction.homEquiv_naturality_right]
  exact (derivationEquiv_comp_d D (op X.unop.1) _ _ (op X.unop.2) x).trans
    (congrArg _ (cotangentUncurryDerivationEquiv_d D N b X x).symm)

/-- **`ε^*Ω_{𝒫/π^{-1}𝒜}` is the uncurrying of the base-changed simplicial differentials.** Both
corepresent the functor `𝒩 ↦ Der_{π^{-1}𝒜}(𝒫, ε_*𝒩)` on sheaves of `π^{-1}ℬ`-modules on `Δ × C`,
with one and the same action of a morphism of coefficient modules, so they are canonically
isomorphic, for any choice `D` of the base-changed simplicial module. -/
def extendAugmentationDifferentialsUncurryIso (D : CotangentSimplicialModuleData J f) :
    (extendAugmentationScalars J f).obj (simplicialDifferentials J f) ≅
      (uncurryMod C J (targetRing J (B := B))).obj D.object :=
  isoOfHomEquivs (extendDifferentialsDerivationEquiv J f)
    (cotangentUncurryDerivationEquiv D)
    (fun k d => d.postcomp
      ((SheafOfModules.restrictScalars (simplicialAugmentationRing J f)).map k).val)
    (fun a k => extendDifferentialsDerivationEquiv_naturality J f a k)
    (fun b k => cotangentUncurryDerivationEquiv_naturality D b k)

end CategoryTheory.Sheaf

end
