module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsLocalIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TrilinearTensorSheaf
public import StacksCore.Tactic.StacksAttribute

/-! # Base change of bilinear and trilinear pairings of sheaves of modules

Let `θ : A₁ ⟶ A₂` be a morphism of presheaves of commutative rings on a site `(C, J)` whose
underlying presheaves of rings are sheaves, and let `F`, `G`, `H` be sheaves of `A₁`-modules and
`N` a sheaf of `A₂`-modules. A pairing of the extensions of scalars `A₂ ⊗_{A₁} F` and
`A₂ ⊗_{A₁} G` with values in `N` which is `A₂`-bilinear is the same thing as a pairing of `F`
and `G` with values in `N` read as a sheaf of `A₁`-modules which is `A₁`-bilinear:

`Bilin_{A₁}(F × G, N|_{A₁}) = Bilin_{A₂}(A₂ ⊗_{A₁} F × A₂ ⊗_{A₁} G, N)`.

This is **step 4** of the chain of bijections recorded in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InverseImageTensor`, the last one of the five that
chain was missing. Applied to the inverse-image form `f⁻¹O_D ⟶ O_C` of the structure map of a
morphism of ringed topoi — along which extension of scalars is the second half of the pullback
of Stacks 03D6 part (2) — it reads
`Bilin_{f⁻¹O_D}(f⁻¹F × f⁻¹G, N|_{f⁻¹O_D}) = Bilin_{O_C}(f^*F × f^*G, N)`.

## Main definitions

* `Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso₃`: base change of a *double* tensor
  product sheaf, `A₂ ⊗_{A₁} ((F ⊗_{A₁} G) ⊗_{A₁} H) ≅
  ((A₂ ⊗_{A₁} F) ⊗_{A₂} (A₂ ⊗_{A₁} G)) ⊗_{A₂} (A₂ ⊗_{A₁} H)`.
* `Stacks.SheafOfModules.extendScalarsBilinearEquiv`: **step 4**, the base change of bilinear
  pairings.
* `Stacks.SheafOfModules.extendScalarsTrilinearEquiv`: the three-variable form of step 4, which
  is what the associativity constraint of the pullback consumes.

## Main results

* `Stacks.SheafOfModules.extendScalarsBilinearEquiv_naturality`: step 4 is natural in the sheaf
  of values. This is what the Yoneda step of Tag 03EL needs of it; steps 1, 2, 3 and 5 have
  their naturality in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BilinearNaturality`. The
  naturality of the trilinear bijection is
  `Stacks.SheafOfModules.extendScalarsTrilinearEquiv_naturality` of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsTrilinearNaturality`, together with
  the trilinear analogues of `Stacks.SheafOfModules.IsBilinearPairing.comp` and of
  `Stacks.SheafOfModules.bilinearEquivTensorSheafHom_naturality` which it is built from.

## Implementation notes

Both bijections are composites of four bijections which are already available, and no square of
linearity has to be transported by hand. Writing `T₁` for the tensor product sheaf over `A₁` and
`T₂` for the one over `A₂`, the binary chain is

1. `Bilin_{A₁}(F × G, N|_{A₁}) = Hom_{A₁}(T₁ F G, N|_{A₁})`, the universal property of the
   tensor product sheaf, `Stacks.SheafOfModules.bilinearEquivTensorSheafHom`;
2. `Hom_{A₁}(T₁ F G, N|_{A₁}) = Hom_{A₂}(A₂ ⊗_{A₁} T₁ F G, N)`, Stacks 03CZ,
   `Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction`;
3. `Hom_{A₂}(A₂ ⊗_{A₁} T₁ F G, N) = Hom_{A₂}(T₂ (A₂ ⊗_{A₁} F) (A₂ ⊗_{A₁} G), N)`, base change
   of a tensor product, `Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso`;
4. `Hom_{A₂}(T₂ (A₂ ⊗_{A₁} F) (A₂ ⊗_{A₁} G), N) =
   Bilin_{A₂}(A₂ ⊗_{A₁} F × A₂ ⊗_{A₁} G, N)`, the universal property again, over `A₂`.

So the whole content of step 4 is that extension of scalars is monoidal, which is
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso`, plus the fact that the tensor
product sheaf represents pairings on both sides. In particular step 4 needs no analogue of
`Stacks.SheafOfModules.square_transport_iff`: unlike step 3, where the two sides live over
different sites and `f⁻¹` is only a left adjoint, here both sides live over the same site and
the comparison is an honest isomorphism of sheaves of modules.

The trilinear chain is the same with `Stacks.SheafOfModules.trilinearEquivTensorSheafHom` in
place of `Stacks.SheafOfModules.bilinearEquivTensorSheafHom` and
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso₃` in place of
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso`. The first of those two is built from
the second by applying base change to the outer tensor product and then correcting the inner
factor, which needs the tensor product sheaf to be functorial in its left argument; that is the
sheafification of a tensor of morphisms of presheaves of modules, and
`Stacks.SheafOfModules.monoidalCategoryPresheafOfModules` has to be a local instance for that
tensor to elaborate, exactly as in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TrilinearTensorSheaf`.

Only one coefficient universe occurs here, because extension of scalars along a morphism of
presheaves of commutative rings keeps both rings in one universe; the two independent universes
`w` and `w'` of `Stacks.SheafOfModules.inverseImageBilinearEquiv` are the coefficient universes
of the two *sites* a morphism of topoi relates, and step 4 happens on one site.

Nothing here carries a `@[stacks]` attribute: base change of pairings is an auxiliary of Tag
03EL and not a tagged statement of the source, exactly as for
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso`.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Limits CategoryTheory.Sheaf
open Stacks.Sheaves.RingedToposModules

universe w v u

/-! ## Base change of a double tensor product sheaf -/

namespace Stacks.Sheaves.RingedToposModules

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

section TensorIso₃

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₁))
  (h₂ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₂))

/-- **Base change of a double tensor product of sheaves of modules.** Extension of scalars along
`θ : A₁ ⟶ A₂` carries `(F ⊗_{A₁} G) ⊗_{A₁} H` to
`((A₂ ⊗_{A₁} F) ⊗_{A₂} (A₂ ⊗_{A₁} G)) ⊗_{A₂} (A₂ ⊗_{A₁} H)`. It is
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso` applied to the outer tensor product,
followed by its own image in the left argument of the outer tensor product over `A₂`. -/
def extendScalarsTensorIso₃ (F G H : SheafOfModules.{w} (commRingSheaf J A₁ h₁)) :
    (extendScalars J θ h₁ h₂).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁ (forget₂ CommRingCat RingCat) h₁⟩).obj
          (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁ (forget₂ CommRingCat RingCat) h₁⟩).obj
          (F)).obj (G))))).obj (H))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨A₂, Presheaf.isSheaf_of_isSheaf_comp _ A₂ (forget₂ CommRingCat RingCat) h₂⟩).obj
          (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨A₂, Presheaf.isSheaf_of_isSheaf_comp _ A₂ (forget₂ CommRingCat RingCat) h₂⟩).obj
          (((extendScalars J θ h₁ h₂).obj F))).obj (((extendScalars J θ h₁ h₂).obj
              G)))))).obj (((extendScalars J θ h₁ h₂).obj H))) :=
  extendScalarsTensorIso θ h₁ h₂
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁ (forget₂ CommRingCat RingCat) h₁⟩).obj (F)).obj
        (G))) H ≪≫
    (PresheafOfModules.sheafification (R := commRingSheaf J A₂ h₂) (𝟙 _)).mapIso
      (((SheafOfModules.forget (commRingSheaf J A₂ h₂)).mapIso
          (extendScalarsTensorIso θ h₁ h₂ F G)) ⊗ᵢ
        Iso.refl ((extendScalars J θ h₁ h₂).obj H).val)

end TensorIso₃

end Stacks.Sheaves.RingedToposModules

/-! ## Base change of bilinear and trilinear pairings -/

namespace Stacks.SheafOfModules

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules

section BaseChange

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₁))
  (h₂ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₂))

/-- **Base change of bilinear pairings**, step 4 of the chain of Tag 03EL. An `A₁`-bilinear
pairing of `F` and `G` with values in `N` restricted to `A₁` is the same thing as an
`A₂`-bilinear pairing of the extensions of scalars `A₂ ⊗_{A₁} F` and `A₂ ⊗_{A₁} G` with values
in `N`:

`Bilin_{A₁}(F × G, N|_{A₁}) = Bilin_{A₂}(A₂ ⊗_{A₁} F × A₂ ⊗_{A₁} G, N)`.

Along the inverse-image form of the structure map of a morphism of ringed topoi this is the
equality `Bilin_{f⁻¹O_D}(f⁻¹F × f⁻¹G, N|_{f⁻¹O_D}) = Bilin_{O_C}(f^*F × f^*G, N)`, the step the
proof of Tag 03EL calls base change. -/
def extendScalarsBilinearEquiv (F G : SheafOfModules.{w} (commRingSheaf J A₁ h₁))
    (N : SheafOfModules.{w} (commRingSheaf J A₂ h₂)) :
    { q : moduleSheaf (commRingSheaf J A₁ h₁) F ⨯ moduleSheaf (commRingSheaf J A₁ h₁) G ⟶
        moduleSheaf (commRingSheaf J A₁ h₁)
          ((SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂)).obj N) //
      IsBilinearPairing (commRingSheaf J A₁ h₁) q } ≃
      { p : moduleSheaf (commRingSheaf J A₂ h₂) ((extendScalars J θ h₁ h₂).obj F) ⨯
          moduleSheaf (commRingSheaf J A₂ h₂) ((extendScalars J θ h₁ h₂).obj G) ⟶
            moduleSheaf (commRingSheaf J A₂ h₂) N //
        IsBilinearPairing (commRingSheaf J A₂ h₂) p } :=
  bilinearEquivTensorSheafHom.trans
    (((extendRestrictScalarsAdjunction J θ h₁ h₂).homEquiv
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁ (forget₂ CommRingCat RingCat) h₁⟩).obj
          (F)).obj (G))) N).symm.trans
      (((extendScalarsTensorIso θ h₁ h₂ F G).homCongr (Iso.refl N)).trans
        bilinearEquivTensorSheafHom.symm))

/-- **Base change of trilinear pairings**, the three-variable form of step 4 of the chain of
Tag 03EL:

`Tri_{A₁}(F × G × H, N|_{A₁}) =
Tri_{A₂}(A₂ ⊗_{A₁} F × A₂ ⊗_{A₁} G × A₂ ⊗_{A₁} H, N)`.

This is the form the associativity constraint of the pullback of sheaves of modules consumes,
since the two bracketings of a triple tensor product are compared through the pairings of three
modules at once. -/
def extendScalarsTrilinearEquiv (F G H : SheafOfModules.{w} (commRingSheaf J A₁ h₁))
    (N : SheafOfModules.{w} (commRingSheaf J A₂ h₂)) :
    { q : (moduleSheaf (commRingSheaf J A₁ h₁) F ⨯ moduleSheaf (commRingSheaf J A₁ h₁) G) ⨯
        moduleSheaf (commRingSheaf J A₁ h₁) H ⟶
          moduleSheaf (commRingSheaf J A₁ h₁)
            ((SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂)).obj N) //
      IsTrilinearPairing (commRingSheaf J A₁ h₁) q } ≃
      { p : (moduleSheaf (commRingSheaf J A₂ h₂) ((extendScalars J θ h₁ h₂).obj F) ⨯
            moduleSheaf (commRingSheaf J A₂ h₂) ((extendScalars J θ h₁ h₂).obj G)) ⨯
          moduleSheaf (commRingSheaf J A₂ h₂) ((extendScalars J θ h₁ h₂).obj H) ⟶
            moduleSheaf (commRingSheaf J A₂ h₂) N //
        IsTrilinearPairing (commRingSheaf J A₂ h₂) p } :=
  trilinearEquivTensorSheafHom.trans
    (((extendRestrictScalarsAdjunction J θ h₁ h₂).homEquiv
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁ (forget₂ CommRingCat RingCat) h₁⟩).obj
          (((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁ (forget₂ CommRingCat RingCat) h₁⟩).obj
          (F)).obj (G))))).obj (H))) N).symm.trans
      (((extendScalarsTensorIso₃ θ h₁ h₂ F G H).homCongr (Iso.refl N)).trans
        trilinearEquivTensorSheafHom.symm))

/-- Composing on the right commutes with transporting a morphism along an isomorphism of its
source. -/
lemma homCongr_refl_comp {E : Type*} [Category E] {X X' Y Y' : E} (α : X ≅ X') (u : X ⟶ Y)
    (k : Y ⟶ Y') :
    α.homCongr (Iso.refl Y') (u ≫ k) = α.homCongr (Iso.refl Y) u ≫ k := by
  simp [Iso.homCongr]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Base change of bilinear pairings is natural in the sheaf of values.** This is the
naturality the Yoneda step of Tag 03EL needs of step 4; its three ingredients are the naturality
of the universal property of the tensor product sheaf on each side and the right-hand naturality
of the adjunction of Tag 03CZ.

Its two sides spell the index of the sheaves of modules two ways —
`Stacks.Sheaves.RingedToposModules.commRingSheaf J A hA` in
`Stacks.SheafOfModules.bilinearEquivTensorSheafHom` and
`Stacks.SheafOfModules.TensorSheafification.structureSheaf A hA` in the tensor product sheaf —
and the two are definitionally but not syntactically equal, so a `rw` or a `simp only` refuses
the first step while a `congrArg` at default transparency takes it. -/
lemma extendScalarsBilinearEquiv_naturality (F G : SheafOfModules.{w} (commRingSheaf J A₁ h₁))
    {N N' : SheafOfModules.{w} (commRingSheaf J A₂ h₂)} (k : N ⟶ N')
    (q : { q : moduleSheaf (commRingSheaf J A₁ h₁) F ⨯ moduleSheaf (commRingSheaf J A₁ h₁) G ⟶
        moduleSheaf (commRingSheaf J A₁ h₁)
          ((SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂)).obj N) //
      IsBilinearPairing (commRingSheaf J A₁ h₁) q }) :
    extendScalarsBilinearEquiv θ h₁ h₂ F G N'
        ⟨q.1 ≫ (moduleSheafFunctor (commRingSheaf J A₁ h₁)).map
            ((SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂)).map k),
          q.2.comp _⟩ =
      ⟨(extendScalarsBilinearEquiv θ h₁ h₂ F G N q).1 ≫
          (moduleSheafFunctor (commRingSheaf J A₂ h₂)).map k,
        (extendScalarsBilinearEquiv θ h₁ h₂ F G N q).2.comp k⟩ :=
  (congrArg (fun t ↦ (bilinearEquivTensorSheafHom (A := A₂) (hA := h₂)
        (F := (extendScalars J θ h₁ h₂).obj F) (G := (extendScalars J θ h₁ h₂).obj G)
        (N := N')).symm
        ((extendScalarsTensorIso θ h₁ h₂ F G).homCongr (Iso.refl N')
          (((extendRestrictScalarsAdjunction J θ h₁ h₂).homEquiv
              ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨A₁, Presheaf.isSheaf_of_isSheaf_comp _ A₁ (forget₂ CommRingCat RingCat) h₁⟩).obj
          (F)).obj (G))) N').symm t)))
      (bilinearEquivTensorSheafHom_naturality q
        ((SheafOfModules.restrictScalars (commRingSheafMap J θ h₁ h₂)).map k))).trans <| by
    erw [(extendRestrictScalarsAdjunction J θ h₁ h₂).homEquiv_naturality_right_symm,
      homCongr_refl_comp]
    exact bilinearEquivTensorSheafHom_symm_naturality (A := A₂) (hA := h₂)
      (F := (extendScalars J θ h₁ h₂).obj F) (G := (extendScalars J θ h₁ h₂).obj G) _ k

end BaseChange

end Stacks.SheafOfModules

end
