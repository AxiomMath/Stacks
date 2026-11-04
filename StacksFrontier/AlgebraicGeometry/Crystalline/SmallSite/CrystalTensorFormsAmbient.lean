module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos
public import StacksFrontier.AlgebraicGeometry.Crystalline.DpDifferentialsAffineUnit
public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondExteriorPowerAffineSections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalIntegrableConnection
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.DifferentialFormsLocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SheafifySections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.TensorRestrictionVanishing

/-!
# `(F ⊗_{𝒪_{X/S}} Ω^i_{X/S})_T = F_T ⊗_{𝒪_T} Ω^i_{T/S,δ}` on the small crystalline site

Fix a global crystalline situation of [Stacks, Tag 07MF], a sheaf of `𝒪_{X/S}`-modules `F` on the
small crystalline site `Cris(X/S)` and an object `A = (U, T, δ)`.  The sheaf
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` of `...SmallSite.tensorDifferentialFormsSheaf` is the sheafification of
the presheaf `A ↦ F(A) ⊗_{Γ(T, 𝒪_T)} Ω^i_{X/S}(A)`.  This module identifies its restriction to the
ambient scheme `T` with the tensor product `F_T ⊗_{𝒪_T} Ω^i_{T/S,δ}` of sheaves of `𝒪_T`-modules,
for `i = 1, 2`, with no hypothesis on `F`:

`(F ⊗ Ω^i_{X/S})_T ≅ F_T ⊗_{𝒪_T} Ω^i_{T/S,δ}`.

This is [Stacks, Tag 07IZ] (`(Ω_{X/S})_T = Ω_{T/S,δ}`) carried through the tensor product and
the exterior power, and it is what lets the canonical connection of [Stacks, Tag 07J6], which the
proof builds on each `T`, be read as a map of sheaves on `Cris(X/S)`.

## The argument

The restriction to `T` of a crystalline sheafification is the Zariski sheafification of the
restriction (`...CrystallineThickening.restrictOpenSheafifyIso`), so it suffices to exhibit a
morphism from the restricted presheaf `W ↦ F(A|_W) ⊗ Ω^i_{X/S}(A|_W)` to `F_T ⊗ Ω^i_{T/S,δ}` which
is locally injective and locally surjective.  The morphism is `x ⊗ ω ↦ x ⊗ ω`, read through the
comparison `Ω^i_{X/S}(A|_W) ⟶ Γ(W, Ω^i_{T/S,δ})`.  It factors as a map to the presheaf tensor
product `W ↦ Γ(W, F_T) ⊗ Γ(W, Ω^i_{T/S,δ})` followed by the sheafification unit of the tensor
product sheaf; the second is locally bijective, and the first is bijective over every affine open
`W` of `T` lying over an affine open of `S` — because there the comparison of differential forms is
bijective by [Stacks, Tag 07IY] — and such opens form a basis of `T`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `FormsComparison` — a comparison of `Ω^i_{X/S}` with a sheaf of `𝒪_T`-modules on the ambient
  scheme, bijective over the affine opens lying over affine opens of the base; `formsComparisonOne`
  and `formsComparisonTwo` are those of [Stacks, Tag 07IZ] with `Ω_{T/S,δ}` and `Ω²_{T/S,δ}`.
* `tensorFormsAmbientUnit` — the comparison morphism `(F ⊗ Ω^i_{X/S})|_T ⟶ F_T ⊗ N` of presheaves,
  `x ⊗ ω ↦ x ⊗ ω`.
* `tensorFormsAmbientIso` — **the identification** `(F ⊗ Ω^i_{X/S})_T ≅ F_T ⊗_{𝒪_T} N`, at the
  coefficient universe `u + 1`.

## Main results

* `tensorFormsAmbientIso_hom_app_toSheafify` — the identification is `x ⊗ ω ↦ x ⊗ ω` on the image
  of the presheaf tensor product.
* `Crystalline.zariski_eq_of_generators` and `zariski_eq_of_tmul` — two compatible families of maps
  into a Zariski sheaf agree once they agree on the image of a locally surjective morphism; this is
  how identities between maps out of `F_T ⊗ N` are checked on pure tensors.

## References

* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Section 60.15, Tag 07J5](https://stacks.math.columbia.edu/tag/07J5)
* [Stacks Project, Lemma 60.15.1, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open TopologicalSpace
open scoped TensorProduct

universe v w u

noncomputable section

namespace Crystalline

/-! ### Zariski-local tools -/

section Local

variable {X : Scheme.{u}}

/-- **Two sections of a Zariski sheaf of abelian groups which agree on a covering sieve agree.** -/
theorem zariski_eq_of_locally_eq {Z : (X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{max u w}}
    (hZ : Presheaf.IsSheaf (Opens.grothendieckTopology X) Z) {W : X.Opens}
    (s t : Z.obj (op W)) {R : Sieve W} (hR : R ∈ Opens.grothendieckTopology X W)
    (h : ∀ ⦃V : X.Opens⦄ (g : V ⟶ W), R g → Z.map g.op s = Z.map g.op t) : s = t := by
  have hsep : Presieve.IsSeparated (Opens.grothendieckTopology X)
      (Z ⋙ forget AddCommGrpCat.{max u w}) := by
    apply Presieve.IsSheaf.isSeparated
    rw [← isSheaf_iff_isSheaf_of_type]
    exact ((sheafCompose _ (forget AddCommGrpCat.{max u w})).obj ⟨Z, hZ⟩).property
  exact (hsep R hR).ext (fun _ g hg ↦ h g hg)

/-- Sections `s, t` of a Zariski sheaf agree once their restrictions to every open `V ≤ W` agree
whenever `z : Q(W)` restricts to the image of a section of `P(V)` under a locally surjective `e`. -/
private theorem eq_of_forall_image {P Q : (X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{v}}
    {Z : (X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{max u w}} (e : P ⟶ Q)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) e]
    (hZ : Presheaf.IsSheaf (Opens.grothendieckTopology X) Z) {W : X.Opens} (z : Q.obj (op W))
    (s t : Z.obj (op W))
    (h : ∀ (V : X.Opens) (hV : V ≤ W) (p : P.obj (op V)),
      e.app (op V) p = Q.map (homOfLE hV).op z →
        Z.map (homOfLE hV).op s = Z.map (homOfLE hV).op t) : s = t := by
  refine zariski_eq_of_locally_eq hZ _ _
    (Presheaf.imageSieve_mem (Opens.grothendieckTopology X) e z) fun V g ⟨p, hp⟩ ↦ ?_
  have hV : V ≤ W := leOfHom g
  obtain rfl : g = homOfLE hV := Subsingleton.elim _ _
  exact h V hV p hp

/-- **Two compatible families of additive maps into a Zariski sheaf which agree on the image of a
locally surjective morphism agree.**  The families are indexed by the opens inside a fixed open
`W` and commute with restriction; every section of the source is locally in the image. -/
theorem zariski_addMonoidHom_eq {P Q : (X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{v}}
    {Z : (X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{max u w}} (e : P ⟶ Q)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) e]
    (hZ : Presheaf.IsSheaf (Opens.grothendieckTopology X) Z) {W : X.Opens}
    (φ ψ : ∀ V : X.Opens, V ≤ W → Q.obj (op V) →+ Z.obj (op V))
    (hφ : ∀ (V V' : X.Opens) (hV : V ≤ W) (hV' : V' ≤ W) (h : V' ≤ V) (z : Q.obj (op V)),
      Z.map (homOfLE h).op (φ V hV z) = φ V' hV' (Q.map (homOfLE h).op z))
    (hψ : ∀ (V V' : X.Opens) (hV : V ≤ W) (hV' : V' ≤ W) (h : V' ≤ V) (z : Q.obj (op V)),
      Z.map (homOfLE h).op (ψ V hV z) = ψ V' hV' (Q.map (homOfLE h).op z))
    (he : ∀ (V : X.Opens) (hV : V ≤ W) (p : P.obj (op V)),
      φ V hV (e.app (op V) p) = ψ V hV (e.app (op V) p))
    (z : Q.obj (op W)) : φ W le_rfl z = ψ W le_rfl z := by
  refine eq_of_forall_image e hZ z _ _ fun V hV p hp ↦ ?_
  refine (hφ W V le_rfl hV hV z).trans (Eq.trans ?_ (hψ W V le_rfl hV hV z).symm)
  rw [← hp]
  exact he V hV p

/-- **Two compatible families of maps into a Zariski sheaf, depending on a parameter that restricts
along with the open, which agree on the image of a locally surjective morphism agree.** -/
theorem zariski_eq_of_generators {P Q : (X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{v}}
    {Z : (X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{max u w}} (e : P ⟶ Q)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) e]
    (hZ : Presheaf.IsSheaf (Opens.grothendieckTopology X) Z) {Ω : X.Opens → Type*}
    (res : ∀ {V V' : X.Opens}, V' ≤ V → Ω V → Ω V')
    (L R : ∀ V : X.Opens, Ω V → Q.obj (op V) → Z.obj (op V))
    (hL : ∀ (V V' : X.Opens) (h : V' ≤ V) (ω : Ω V) (z : Q.obj (op V)),
      Z.map (homOfLE h).op (L V ω z) = L V' (res h ω) (Q.map (homOfLE h).op z))
    (hR : ∀ (V V' : X.Opens) (h : V' ≤ V) (ω : Ω V) (z : Q.obj (op V)),
      Z.map (homOfLE h).op (R V ω z) = R V' (res h ω) (Q.map (homOfLE h).op z))
    (he : ∀ (V : X.Opens) (ω : Ω V) (p : P.obj (op V)), L V ω (e.app (op V) p) =
      R V ω (e.app (op V) p))
    (V : X.Opens) (ω : Ω V) (z : Q.obj (op V)) : L V ω z = R V ω z := by
  refine eq_of_forall_image e hZ z _ _ fun V' hV p hp ↦ ?_
  refine (hL V V' hV ω z).trans (Eq.trans ?_ (hR V V' hV ω z).symm)
  rw [← hp]
  exact he V' (res hV ω) p

/-- **A morphism of Zariski presheaves which is injective over the members of a basis is locally
injective.** -/
theorem isLocallyInjective_of_injective_basis {P Q : (X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{v}}
    (e : P ⟶ Q) (B : X.Opens → Prop)
    (hB : ∀ (U : X.Opens) (x : X), x ∈ U → ∃ W, B W ∧ x ∈ W ∧ W ≤ U)
    (he : ∀ W, B W → Function.Injective (e.app (op W))) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) e := by
  refine ⟨fun {U} x y hxy ↦ ?_⟩
  intro p hp
  obtain ⟨W, hW, hpW, hWU⟩ := hB U.unop p hp
  refine ⟨W, homOfLE hWU, ?_, hpW⟩
  apply he W hW
  show e.app (op W) (P.map (homOfLE hWU).op x) = e.app (op W) (P.map (homOfLE hWU).op y)
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
  exact congrArg _ hxy

/-- **A morphism of Zariski presheaves which is surjective over the members of a basis is locally
surjective.** -/
theorem isLocallySurjective_of_surjective_basis {P Q : (X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{v}}
    (e : P ⟶ Q) (B : X.Opens → Prop)
    (hB : ∀ (U : X.Opens) (x : X), x ∈ U → ∃ W, B W ∧ x ∈ W ∧ W ≤ U)
    (he : ∀ W, B W → Function.Surjective (e.app (op W))) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) e := by
  refine ⟨fun {U} s ↦ ?_⟩
  intro p hp
  obtain ⟨W, hW, hpW, hWU⟩ := hB U p hp
  obtain ⟨t, ht⟩ := he W hW (Q.map (homOfLE hWU).op s)
  exact ⟨W, homOfLE hWU, ⟨t, ht⟩, hpW⟩

end Local

/-- **The identification `Γ(W, 𝒪_X) ≅ Γ(W, 𝒪_W)` of Mathlib is `Crystalline.openTopRes`.** -/
theorem topIso_inv_eq_openTopRes {X : Scheme.{u}} (W : X.Opens) :
    W.topIso.inv = openTopRes W := by
  rw [openTopRes_eq, Scheme.Opens.topIso]
  rfl

namespace GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-- **The two identifications of the restriction of `𝒪_{X/S}` with `𝒪_T` agree on sections.** -/
theorem ringRestrictionSheafStructureIso_inv_app_apply (A : Thickening S)
    (W : A.thickening.target.scheme.Opens)
    (r : ↑(A.thickening.target.scheme.ringCatSheaf.obj.obj (op W))) :
    ((Thickening.ringRestrictionSheafStructureIso A).inv.hom.app (op W)).hom r =
      ((Thickening.restrictOpenRingHom A).app (op W)).hom r := by
  show W.topIso.inv.hom r = _
  rw [topIso_inv_eq_openTopRes]
  rfl

/-! ### A basis of the ambient scheme -/

/-- An open of the ambient scheme of an object of `CRIS(X/S)` is **affine over affine** if it is
affine and maps into an affine open of the base. -/
def IsAffineOverAffineOpen (A : Thickening S) (W : A.thickening.target.scheme.Opens) : Prop :=
  IsAffineOpen W ∧ ∃ V : S.S.scheme.Opens, IsAffineOpen V ∧ W ≤ A.toBase.hom ⁻¹ᵁ V

/-- **The affine-over-affine opens form a basis of the ambient scheme.** -/
theorem exists_isAffineOverAffineOpen (A : Thickening S)
    (U : A.thickening.target.scheme.Opens) (x : A.thickening.target.scheme) (hx : x ∈ U) :
    ∃ W, IsAffineOverAffineOpen A W ∧ x ∈ W ∧ W ≤ U := by
  obtain ⟨V, hV, hxV, -⟩ := (Opens.isBasis_iff_nbhd.mp S.S.scheme.isBasis_affineOpens)
    (show A.toBase.hom.base x ∈ (⊤ : S.S.scheme.Opens) from trivial)
  obtain ⟨W, hW, hxW, hWU⟩ := (Opens.isBasis_iff_nbhd.mp
    A.thickening.target.scheme.isBasis_affineOpens)
    (show x ∈ U ⊓ A.toBase.hom ⁻¹ᵁ V from ⟨hx, hxV⟩)
  exact ⟨W, ⟨hW, V, hV, hWU.trans inf_le_right⟩, hxW, hWU.trans inf_le_left⟩

end GlobalCrystallineSituation

/-! ### Tensor products over isomorphic rings -/

section TensorMap

variable {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂] (σ : R₁ →+* R₂)
  {M₁ N₁ M₂ N₂ : Type*} [AddCommGroup M₁] [AddCommGroup N₁] [AddCommGroup M₂] [AddCommGroup N₂]
  [Module R₁ M₁] [Module R₁ N₁] [Module R₂ M₂] [Module R₂ N₂]
  (f : M₁ →+ M₂) (g : N₁ →+ N₂) (hf : ∀ (r : R₁) (m : M₁), f (r • m) = σ r • f m)
  (hg : ∀ (r : R₁) (n : N₁), g (r • n) = σ r • g n)

/-- **The tensor product of two semilinear maps along a ring homomorphism**, as an additive map
`M₁ ⊗[R₁] N₁ → M₂ ⊗[R₂] N₂`, `m ⊗ n ↦ f m ⊗ g n`. -/
def tensorMapSemilinear : M₁ ⊗[R₁] N₁ →+ M₂ ⊗[R₂] N₂ :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun m ↦ (TensorProduct.mk R₂ M₂ N₂ (f m)).toAddMonoidHom.comp g)
      (fun m m' ↦ by
        ext n
        simp [TensorProduct.add_tmul]))
    (fun r m n ↦ by
      change f (r • m) ⊗ₜ[R₂] g n = f m ⊗ₜ[R₂] g (r • n)
      rw [hf, hg, TensorProduct.smul_tmul])

/-- The tensor product of two semilinear maps on a pure tensor: `m ⊗ n ↦ f m ⊗ g n`. -/
@[simp]
theorem tensorMapSemilinear_tmul (m : M₁) (n : N₁) :
    tensorMapSemilinear σ f g hf hg (m ⊗ₜ n) = f m ⊗ₜ g n := rfl

/-- The tensor product of two semilinear maps is semilinear. -/
theorem tensorMapSemilinear_smul (r : R₁) (z : M₁ ⊗[R₁] N₁) :
    tensorMapSemilinear σ f g hf hg (r • z) = σ r • tensorMapSemilinear σ f g hf hg z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul m n =>
    rw [TensorProduct.smul_tmul', tensorMapSemilinear_tmul, tensorMapSemilinear_tmul, hf,
      TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

omit [AddCommGroup M₂] [AddCommGroup N₂] [Module R₂ M₂] [Module R₂ N₂] in
/-- **Two additive maps out of a tensor product which agree on pure tensors agree.** -/
theorem addMonoidHom_tensor_ext {P : Type*} [AddCommGroup P] {f g : M₁ ⊗[R₁] N₁ →+ P}
    (h : ∀ (m : M₁) (n : N₁), f (m ⊗ₜ n) = g (m ⊗ₜ n)) : f = g := by
  refine AddMonoidHom.ext fun z ↦ ?_
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul m n => exact h m n
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **The tensor product of two semilinear bijections along a ring isomorphism is bijective.** -/
theorem bijective_tensorMapSemilinear (σ : R₁ ≃+* R₂) (f : M₁ ≃+ M₂) (g : N₁ ≃+ N₂)
    (hf : ∀ (r : R₁) (m : M₁), f (r • m) = σ r • f m)
    (hg : ∀ (r : R₁) (n : N₁), g (r • n) = σ r • g n) :
    Function.Bijective
      (tensorMapSemilinear σ.toRingHom f.toAddMonoidHom g.toAddMonoidHom hf hg) := by
  have hf' : ∀ (r : R₂) (m : M₂), f.symm (r • m) = σ.symm r • f.symm m := fun r m ↦ by
    apply f.injective
    rw [AddEquiv.apply_symm_apply, hf, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have hg' : ∀ (r : R₂) (n : N₂), g.symm (r • n) = σ.symm r • g.symm n := fun r n ↦ by
    apply g.injective
    rw [AddEquiv.apply_symm_apply, hg, RingEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  let inv := tensorMapSemilinear σ.symm.toRingHom f.symm.toAddMonoidHom g.symm.toAddMonoidHom
    hf' hg'
  have h1 : ∀ z, inv (tensorMapSemilinear σ.toRingHom f.toAddMonoidHom g.toAddMonoidHom hf hg z) =
      z := fun z ↦ by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [inv]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have h2 : ∀ z, tensorMapSemilinear σ.toRingHom f.toAddMonoidHom g.toAddMonoidHom hf hg (inv z) =
      z := fun z ↦ by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul m n => simp [inv]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

end TensorMap

namespace GlobalCrystallineSituation.SmallSite

attribute [local instance] monoidalCategorySchemeModules

variable {S : GlobalCrystallineSituation.{u}} (F : SheafOfModules.{u} (structureSheaf S))
  (A : CrystallineThickening S)

/-! ### The comparison of rings -/

/-- The sections of a sheaf of `𝒪_{X/S}`-modules over an object, as a module over the section ring
in the small-site spelling. -/
@[instance_reducible]
def moduleCrysFormRingSections (B : CrystallineThickening S) :
    Module (crysFormRing S B) (F.val.obj (op B)) :=
  inferInstanceAs (Module ((structureSheaf S).val.obj (op B)) (F.val.obj (op B)))

attribute [local instance] moduleCrysFormRingSections

/-- The ring of sections of `𝒪_T` over an open, in the `RingCat`-valued spelling of
`AlgebraicGeometry.Scheme.ringCatSheaf`, is commutative. -/
@[instance_reducible]
def commRingRingCatSheafSections {X : Scheme.{u}} (W : X.Opens) :
    CommRing ↑(X.ringCatSheaf.obj.obj (op W)) :=
  inferInstanceAs (CommRing Γ(X, W))

attribute [local instance] commRingRingCatSheafSections

/-- **The section ring of `𝒪_{X/S}` over `A|_W` is the ring of sections of `𝒪_T` over `W`**, the
inverse of `Crystalline.openTopRes`. -/
def sectionRingEquiv (W : A.obj.thickening.target.scheme.Opens) :
    crysFormRing S (A.restrictOpen W) ≃+*
      ↑(A.obj.thickening.target.scheme.ringCatSheaf.obj.obj (op W)) :=
  (openTopResEquiv A W).symm

/-- The structure morphism of the restriction to `W` read on section rings inverts
`sectionRingEquiv`. -/
theorem restrictOpenRingHom_sectionRingEquiv (W : A.obj.thickening.target.scheme.Opens)
    (r : crysFormRing S (A.restrictOpen W)) :
    ((Thickening.restrictOpenRingHom A.obj).app (op W)).hom (sectionRingEquiv A W r) = r :=
  (openTopResEquiv A W).apply_symm_apply r

/-! ### The comparison of differential forms in degree one -/

/-- The degree-one identification `Ω^1_{X/S} = Ω_{X/S}` on the sections over an object of
`Cris(X/S)`, in the small-site spelling. -/
def formsOneEquiv (B : CrystallineThickening S) :
    (crysDifferentialForms S 1).obj (op B) ≃ₗ[crysFormRing S B] (crysDifferentials S).obj (op B) :=
  crysFormsOneApp S B.obj

/-- **The comparison `Ω^1_{X/S}(A|_W) ⟶ Γ(W, Ω_{T/S,δ})` of [Stacks, Tag 07IZ]**, the degree-one
identification `⋀¹ = id` followed by `...restrictedToSheaf`. -/
def formsCompOne (W : A.obj.thickening.target.scheme.Opens) :
    (crysDifferentialForms S 1).obj (op (A.restrictOpen W)) →+
      (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.obj
        (op W) :=
  ((restrictedToSheaf A.obj).app (op W)).hom.toAddMonoidHom.comp
    (formsOneEquiv (A.restrictOpen W)).toLinearMap.toAddMonoidHom

/-- The comparison of differential forms is semilinear over `sectionRingEquiv`. -/
theorem formsCompOne_smul (W : A.obj.thickening.target.scheme.Opens)
    (r : crysFormRing S (A.restrictOpen W))
    (ω : (crysDifferentialForms S 1).obj (op (A.restrictOpen W))) :
    formsCompOne A W (r • ω) = sectionRingEquiv A W r • formsCompOne A W ω := by
  have h1 := congrArg ((restrictedToSheaf A.obj).app (op W)).hom
    (LinearEquiv.map_smul (formsOneEquiv (A.restrictOpen W)) r ω)
  have h2 : r • formsOneEquiv (A.restrictOpen W) ω =
      (show (restrictedCrysDifferentials S A.obj).obj (op W) from
        (sectionRingEquiv A W r) •
          (show (restrictedCrysDifferentials S A.obj).obj (op W) from
            formsOneEquiv (A.restrictOpen W) ω)) :=
    congrArg (fun c : crysFormRing S (A.restrictOpen W) ↦ c • formsOneEquiv (A.restrictOpen W) ω)
      (restrictOpenRingHom_sectionRingEquiv A W r).symm
  exact h1.trans ((congrArg ((restrictedToSheaf A.obj).app (op W)).hom h2).trans
    (((restrictedToSheaf A.obj).app (op W)).hom.map_smul (sectionRingEquiv A W r) _))

/-- The scalars of `𝒪_T` act on the sections of `F_T` through `sectionRingEquiv`. -/
theorem crysAmbient_smul (W : A.obj.thickening.target.scheme.Opens)
    (r : crysFormRing S (A.restrictOpen W)) (x : F.val.obj (op (A.restrictOpen W))) :
    (show (crysAmbientSchemeModules F A).val.obj (op W) from r • x) =
      sectionRingEquiv A W r • (show (crysAmbientSchemeModules F A).val.obj (op W) from x) :=
  (congrArg (fun c : crysFormRing S (A.restrictOpen W) ↦ c • x)
      (restrictOpenRingHom_sectionRingEquiv A W r).symm).trans
    (congrArg (fun c : crysFormRing S (A.restrictOpen W) ↦ c • x)
      (ringRestrictionSheafStructureIso_inv_app_apply A.obj W (sectionRingEquiv A W r)).symm)

/-- The degree-one identification is natural in the object of `Cris(X/S)`. -/
theorem formsOneEquiv_map {B B' : CrystallineThickening S} (k : B ⟶ B')
    (ω : (crysDifferentialForms S 1).obj (op B')) :
    formsOneEquiv B ((crysDifferentialForms S 1).map k.op ω) =
      (crysDifferentials S).map k.op (formsOneEquiv B' ω) := by
  obtain ⟨ω', rfl⟩ := (formsOneEquiv B').symm.surjective ω
  have e1 : (formsOneEquiv B').symm ω' = (crysFormsOneGen S).app (op B') ω' :=
    crysFormsOneApp_symm_eq_oneGen S B'.obj ω'
  have h := PresheafOfModules.naturality_apply (crysFormsOneGen S) k.op ω'
  refine (congrArg (fun z ↦ formsOneEquiv B ((crysDifferentialForms S 1).map k.op z)) e1).trans ?_
  refine (congrArg (formsOneEquiv B) h.symm).trans ?_
  refine (crysFormsOneApp_oneGen S B.obj _).trans ?_
  exact congrArg ((crysDifferentials S).map k.op) ((formsOneEquiv B').apply_symm_apply ω').symm

/-- The comparison of differential forms commutes with restriction to smaller opens. -/
theorem formsCompOne_naturality {W W' : A.obj.thickening.target.scheme.Opens} (i : W' ⟶ W)
    (ω : (crysDifferentialForms S 1).obj (op (A.restrictOpen W))) :
    formsCompOne A W' ((crysDifferentialForms S 1).map
        ((CrystallineThickening.restrictOpenFunctor A).map i).op ω) =
      (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom).val.map i.op
        (formsCompOne A W ω) :=
  (congrArg ((restrictedToSheaf A.obj).app (op W')).hom
    (formsOneEquiv_map ((CrystallineThickening.restrictOpenFunctor A).map i) ω)).trans
    (PresheafOfModules.naturality_apply (restrictedToSheaf A.obj) i.op _)

/-- **Over an affine open lying over an affine open of the base, the comparison of differential
forms is bijective**: [Stacks, Tag 07IZ] on sections, by [Stacks, Tag 07IY]. -/
theorem bijective_formsCompOne {W : A.obj.thickening.target.scheme.Opens}
    (hW : IsAffineOverAffineOpen A.obj W) : Function.Bijective (formsCompOne A W) := by
  obtain ⟨hW, V, hV, h⟩ := hW
  exact (bijective_restrictedToSheaf_app S A.obj hW h hV).comp
    (formsOneEquiv (A.restrictOpen W)).bijective

/-! ### A comparison of differential forms, abstractly -/

/-- **A comparison of the differential forms of degree `i` on `Cris(X/S)` with a sheaf `N` of
`𝒪_T`-modules on the ambient scheme of an object `A`**: maps `Ω^i_{X/S}(A|_W) ⟶ Γ(W, N)`,
semilinear over `sectionRingEquiv`, compatible with restriction, and bijective over every affine
open of `T` lying over an affine open of the base.  The comparisons used below are the ones of
[Stacks, Tag 07IZ] in degrees one and two. -/
structure FormsComparison (i : ℕ) (N : A.obj.thickening.target.scheme.Modules) where
  /-- The comparison on the sections over an open. -/
  toFun : ∀ W : A.obj.thickening.target.scheme.Opens,
    (crysDifferentialForms S i).obj (op (A.restrictOpen W)) →+ N.val.obj (op W)
  map_smul : ∀ (W : A.obj.thickening.target.scheme.Opens) (r : crysFormRing S (A.restrictOpen W))
    (ω : (crysDifferentialForms S i).obj (op (A.restrictOpen W))),
    toFun W (r • ω) = sectionRingEquiv A W r • toFun W ω
  naturality : ∀ {W W' : A.obj.thickening.target.scheme.Opens} (j : W' ⟶ W)
    (ω : (crysDifferentialForms S i).obj (op (A.restrictOpen W))),
    toFun W' ((crysDifferentialForms S i).map
        ((CrystallineThickening.restrictOpenFunctor A).map j).op ω) =
      N.val.map j.op (toFun W ω)
  /-- The comparison is bijective over every affine open lying over an affine open of the base. -/
  bijective : ∀ W : A.obj.thickening.target.scheme.Opens, IsAffineOverAffineOpen A.obj W →
    Function.Bijective (toFun W)

/-- **The comparison of [Stacks, Tag 07IZ] in degree one**, `Ω^1_{X/S}(A|_W) ⟶ Γ(W, Ω_{T/S,δ})`. -/
def formsComparisonOne :
    FormsComparison A 1 (dpDifferentialsSheaf A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom) where
  toFun := formsCompOne A
  map_smul := formsCompOne_smul A
  naturality := formsCompOne_naturality A
  bijective _ hW := bijective_formsCompOne A hW

/-- The exterior power of the inverse of a linear equivalence is a left inverse of its exterior
power. -/
private theorem powMapₛₗ_symm_powMapₛₗ {R : Type*} [CommRing R]
    {M₁ M₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁] [Module R M₂]
    (n : ℕ) (e : M₁ ≃ₗ[R] M₂) (x : ⋀[R]^n M₁) :
    ExteriorAlgebra.powMapₛₗ n (RingHom.id R) e.symm.toLinearMap
      (ExteriorAlgebra.powMapₛₗ n (RingHom.id R) e.toLinearMap x) = x :=
  (ExteriorAlgebra.powMapₛₗ_eq_comp n e.toLinearMap e.symm.toLinearMap
    (e.symm.toLinearMap.comp e.toLinearMap) (fun _ ↦ rfl) (fun _ ↦ rfl) x).symm.trans
    (ExteriorAlgebra.powMapₛₗ_eq_self n _ (fun _ ↦ rfl) (fun m ↦ e.symm_apply_apply m) x)

/-- **A linear bijection induces a bijection on exterior powers.** -/
theorem _root_.ExteriorAlgebra.bijective_powMapₛₗ_id {R : Type*} [CommRing R]
    {M₁ M₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂] [Module R M₁] [Module R M₂]
    (e : M₁ ≃ₗ[R] M₂) (n : ℕ) :
    Function.Bijective (ExteriorAlgebra.powMapₛₗ n (RingHom.id R) e.toLinearMap) := by
  have h1 := powMapₛₗ_symm_powMapₛₗ n e
  have h2 := powMapₛₗ_symm_powMapₛₗ n e.symm
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

/-- **The sectionwise exterior power of a morphism of presheaves of modules is bijective where
the morphism is.** -/
theorem _root_.PresheafOfModules.bijective_extPowMap_app {C : Type*} [Category C]
    {O : Cᵒᵖ ⥤ CommRingCat.{u}} (n : ℕ) {M M' : PresheafOfModules.{u} (O ⋙ forget₂ _ RingCat)}
    (α : M ⟶ M') (X : Cᵒᵖ) (h : Function.Bijective (α.app X)) :
    Function.Bijective ((PresheafOfModules.extPowMap n α).app X) := by
  let e := LinearEquiv.ofBijective (α.app X).hom h
  have key : ∀ x, PresheafOfModules.extPowSections n M' X
      ((PresheafOfModules.extPowMap n α).app X x) =
        ExteriorAlgebra.powMapₛₗ n (RingHom.id _) e.toLinearMap
          (PresheafOfModules.extPowSections n M X x) := fun x ↦
    Subtype.ext (PresheafOfModules.extPowMap_app_coe n α X x)
  have hb := ExteriorAlgebra.bijective_powMapₛₗ_id e n
  refine ⟨fun x y hxy ↦ ?_, fun z ↦ ?_⟩
  · have := congrArg (PresheafOfModules.extPowSections n M' X) hxy
    rw [key, key] at this
    exact (PresheafOfModules.extPowSections n M X).injective (hb.1 this)
  · obtain ⟨w, hw⟩ := hb.2 (PresheafOfModules.extPowSections n M' X z)
    obtain ⟨x, rfl⟩ := (PresheafOfModules.extPowSections n M X).surjective w
    refine ⟨x, (PresheafOfModules.extPowSections n M' X).injective ?_⟩
    rw [key, hw]

/-- The components of an isomorphism of presheaves of modules are bijective. -/
theorem _root_.PresheafOfModules.bijective_app_of_iso {C : Type*} [Category C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} {M M' : PresheafOfModules.{u} R} (e : M ≅ M') (X : Cᵒᵖ) :
    Function.Bijective (e.hom.app X) :=
  ⟨Function.LeftInverse.injective (g := e.inv.app X)
      (fun x ↦ congrArg (fun φ : M ⟶ M ↦ (φ.app X).hom x) e.hom_inv_id),
    Function.RightInverse.surjective (g := e.inv.app X)
      (fun x ↦ congrArg (fun φ : M' ⟶ M' ↦ (φ.app X).hom x) e.inv_hom_id)⟩

/-- **The comparison `Ω²_{X/S}|_T ⟶ Ω²_{T/S,δ}` of presheaves of `𝒪_T`-modules**: the
identification of the restriction of `Ω²_{X/S}` with the sectionwise exterior square of the
restriction of `Ω_{X/S}`, the exterior square of the comparison `...restrictedToSheaf` of
[Stacks, Tag 07IZ], and the sheafification unit of `Ω²_{T/S,δ}`. -/
def formsCompTwoHom :
    restrictedCrysDifferentialForms S A.obj 2 ⟶
      dpSecondExteriorModules A.obj.thickening.target S.S.scheme A.obj.toBase.hom :=
  (restrictedCrysDifferentialFormsIso S A.obj 2).hom ≫
    PresheafOfModules.extPowMap 2 (restrictedToSheaf A.obj) ≫
      dpSecondExteriorToSheaf A.obj.thickening.target S.S.scheme A.obj.toBase.hom

/-- **The comparison of [Stacks, Tag 07IZ] in degree two**,
`Ω²_{X/S}(A|_W) ⟶ Γ(W, Ω²_{T/S,δ})`. -/
def formsComparisonTwo :
    FormsComparison A 2 (dpSecondExteriorPower A.obj.thickening.target S.S.scheme
      A.obj.toBase.hom) where
  toFun W := ((formsCompTwoHom A).app (op W)).hom.toAddMonoidHom
  map_smul W r ω := by
    have h2 : r • ω = (show (restrictedCrysDifferentialForms S A.obj 2).obj (op W) from
        (sectionRingEquiv A W r) • (show (restrictedCrysDifferentialForms S A.obj 2).obj (op W)
          from ω)) :=
      congrArg (fun c : crysFormRing S (A.restrictOpen W) ↦ c • ω)
        (restrictOpenRingHom_sectionRingEquiv A W r).symm
    exact (congrArg ((formsCompTwoHom A).app (op W)).hom h2).trans
      (((formsCompTwoHom A).app (op W)).hom.map_smul (sectionRingEquiv A W r) _)
  naturality j ω := PresheafOfModules.naturality_apply (formsCompTwoHom A) j.op ω
  bijective W hW := by
    obtain ⟨hW, V, hV, h⟩ := hW
    exact (bijective_dpSecondExteriorToSheaf_app _ _ _ hW).comp
      ((PresheafOfModules.bijective_extPowMap_app 2 (restrictedToSheaf A.obj) (op W)
        (bijective_restrictedToSheaf_app S A.obj hW h hV)).comp
        (PresheafOfModules.bijective_app_of_iso (restrictedCrysDifferentialFormsIso S A.obj 2)
          (op W)))

/-- The degree-one comparison on sections is `formsCompOne`. -/
@[simp]
theorem formsComparisonOne_toFun (V : A.obj.thickening.target.scheme.Opens)
    (ω : (crysDifferentialForms S 1).obj (op (A.restrictOpen V))) :
    (formsComparisonOne A).toFun V ω = formsCompOne A V ω := rfl

variable {A} {i : ℕ} {N : A.obj.thickening.target.scheme.Modules} (c : FormsComparison A i N)

/-- The presheaf tensor product `W ↦ Γ(W, F_T) ⊗_{Γ(W, 𝒪_T)} Γ(W, N)`, as an abelian presheaf on
`T`. -/
abbrev ambientTensorPresheaf (N : A.obj.thickening.target.scheme.Modules) :
    (A.obj.thickening.target.scheme.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (PresheafOfModules.toPresheaf _).obj
    (PresheafOfModules.tensorObj (crysAmbientSchemeModules F A).val N.val)

/-- The tensor product sheaf `F_T ⊗_{𝒪_T} N` on the ambient scheme of `A`. -/
abbrev ambientTensor (N : A.obj.thickening.target.scheme.Modules) :
    A.obj.thickening.target.scheme.Modules :=
  crysAmbientSchemeModules F A ⊗ N

variable {F} in
/-- A pure tensor in the sections over `A|_W` of the presheaf `F ⊗ Ω^i_{X/S}`. -/
abbrev restrTmul (W : A.obj.thickening.target.scheme.Opens)
    (x : F.val.obj (op (A.restrictOpen W)))
    (ω : (crysDifferentialForms S i).obj (op (A.restrictOpen W))) :
    F.val.obj (op (A.restrictOpen W)) ⊗[crysFormRing S (A.restrictOpen W)]
      (crysDifferentialForms S i).obj (op (A.restrictOpen W)) :=
  x ⊗ₜ ω

/-- The comparison on sections over an open `W`: `x ⊗ ω ↦ x ⊗ ω`. -/
def tensorFormsAmbientApp (W : A.obj.thickening.target.scheme.Opens) :
    F.val.obj (op (A.restrictOpen W)) ⊗[crysFormRing S (A.restrictOpen W)]
        (crysDifferentialForms S i).obj (op (A.restrictOpen W)) →+
      (ambientTensorPresheaf F N).obj (op W) :=
  tensorMapSemilinear (M₁ := F.val.obj (op (A.restrictOpen W)))
    (M₂ := (crysAmbientSchemeModules F A).val.obj (op W))
    (sectionRingEquiv A W).toRingHom (AddMonoidHom.id _) (c.toFun W)
    (crysAmbient_smul F A W) (c.map_smul W)

/-- **The comparison morphism `(F ⊗ Ω^i_{X/S})|_T ⟶ F_T ⊗_{p} N`** into the presheaf tensor
product, `x ⊗ ω ↦ x ⊗ ω`. -/
def tensorFormsAmbient : (tensorRestriction A F i).presheaf ⟶ ambientTensorPresheaf F N where
  app W := AddCommGrpCat.ofHom (tensorFormsAmbientApp F c W.unop)
  naturality {W W'} j := by
    ext z
    change tensorFormsAmbientApp F c W'.unop ((tensorRestriction A F i).map j z) =
      (ambientTensorPresheaf F N).map j (tensorFormsAmbientApp F c W.unop z)
    induction z using TensorProduct.induction_on with
    | zero =>
      exact (congrArg (tensorFormsAmbientApp F c W'.unop)
        (map_zero (ConcreteCategory.hom ((tensorRestriction A F i).map j)))).trans
        ((map_zero _).trans ((congrArg (ConcreteCategory.hom ((ambientTensorPresheaf F N).map j))
          (map_zero (tensorFormsAmbientApp F c W.unop))).trans (map_zero _)).symm)
    | tmul x ω =>
      exact congrArg (fun η ↦ _ ⊗ₜ η) (c.naturality j.unop ω)
    | add z z' hz hz' =>
      exact (congrArg (tensorFormsAmbientApp F c W'.unop)
        (map_add (ConcreteCategory.hom ((tensorRestriction A F i).map j)) z z')).trans
        ((map_add _ _ _).trans ((congrArg₂ (· + ·) hz hz').trans
          ((congrArg (ConcreteCategory.hom ((ambientTensorPresheaf F N).map j))
            (map_add (tensorFormsAmbientApp F c W.unop) z z')).trans (map_add _ _ _)).symm))

/-- Over an affine open lying over an affine open of the base, the comparison into the presheaf
tensor product is bijective. -/
theorem bijective_tensorFormsAmbientApp {W : A.obj.thickening.target.scheme.Opens}
    (hW : IsAffineOverAffineOpen A.obj W) :
    Function.Bijective (tensorFormsAmbientApp F c W) :=
  bijective_tensorMapSemilinear (M₁ := F.val.obj (op (A.restrictOpen W)))
    (M₂ := (crysAmbientSchemeModules F A).val.obj (op W))
    (sectionRingEquiv A W) (AddEquiv.refl _)
    (AddEquiv.ofBijective (c.toFun W) (c.bijective W hW))
    (crysAmbient_smul F A W) (c.map_smul W)

/-- The comparison into the presheaf tensor product is locally injective. -/
instance isLocallyInjective_tensorFormsAmbient :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (tensorFormsAmbient F c) :=
  isLocallyInjective_of_injective_basis _ _ (exists_isAffineOverAffineOpen A.obj)
    (fun _ hW ↦ (bijective_tensorFormsAmbientApp F c hW).1)

/-- The comparison into the presheaf tensor product is locally surjective. -/
instance isLocallySurjective_tensorFormsAmbient :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (tensorFormsAmbient F c) :=
  isLocallySurjective_of_surjective_basis _ _ (exists_isAffineOverAffineOpen A.obj)
    (fun _ hW ↦ (bijective_tensorFormsAmbientApp F c hW).2)

/-- **The comparison morphism `(F ⊗ Ω^i_{X/S})|_T ⟶ F_T ⊗ N`**, `x ⊗ ω ↦ x ⊗ ω`: the comparison
into the presheaf tensor product followed by the unit of the tensor product sheaf. -/
def tensorFormsAmbientUnit :
    (tensorRestriction A F i).presheaf ⟶
      ((SheafOfModules.toSheaf _).obj (ambientTensor F N)).obj :=
  tensorFormsAmbient F c ≫ (PresheafOfModules.toPresheaf _).map
    ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.RingedSpace.structureRingSheaf
          (A.obj.thickening.target.scheme.toRingedSpace))
        (𝟙 (Stacks.RingedSpace.structureRingSheaf
          (A.obj.thickening.target.scheme.toRingedSpace)).obj)).unit.app
      (PresheafOfModules.tensorObj
        (O := (A.obj.thickening.target.scheme.toRingedSpace).presheaf)
        ((crysAmbientSchemeModules F A)).val (N).val))

/-- The unit of the tensor product sheaf `F_T ⊗ N` is locally injective. -/
theorem isLocallyInjective_tensorSheafUnit :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      ((PresheafOfModules.toPresheaf
          ((sheafToPresheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme)
            CommRingCat).obj A.obj.thickening.target.scheme.sheaf ⋙
              forget₂ CommRingCat RingCat)).map
        ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf
              (A.obj.thickening.target.scheme.toRingedSpace))
            (𝟙 (Stacks.RingedSpace.structureRingSheaf
              (A.obj.thickening.target.scheme.toRingedSpace)).obj)).unit.app
          (PresheafOfModules.tensorObj
            (O := (A.obj.thickening.target.scheme.toRingedSpace).presheaf)
            ((crysAmbientSchemeModules F A)).val (N).val))) :=
  GrothendieckTopology.W.isLocallyInjective
    ((Opens.grothendieckTopology A.obj.thickening.target.scheme).W_toSheafify _)

/-- The unit of the tensor product sheaf `F_T ⊗ N` is locally surjective. -/
theorem isLocallySurjective_tensorSheafUnit :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      ((PresheafOfModules.toPresheaf
          ((sheafToPresheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme)
            CommRingCat).obj A.obj.thickening.target.scheme.sheaf ⋙
              forget₂ CommRingCat RingCat)).map
        ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf
              (A.obj.thickening.target.scheme.toRingedSpace))
            (𝟙 (Stacks.RingedSpace.structureRingSheaf
              (A.obj.thickening.target.scheme.toRingedSpace)).obj)).unit.app
          (PresheafOfModules.tensorObj
            (O := (A.obj.thickening.target.scheme.toRingedSpace).presheaf)
            ((crysAmbientSchemeModules F A)).val (N).val))) :=
  GrothendieckTopology.W.isLocallySurjective
    ((Opens.grothendieckTopology A.obj.thickening.target.scheme).W_toSheafify _)

/-- The comparison morphism `(F ⊗ Ω^i_{X/S})|_T ⟶ F_T ⊗ N` is locally injective. -/
instance isLocallyInjective_tensorFormsAmbientUnit :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (tensorFormsAmbientUnit F c) :=
  @Presheaf.isLocallyInjective_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (isLocallyInjective_tensorFormsAmbient F c)
    (isLocallyInjective_tensorSheafUnit F (A := A) (N := N))

/-- The comparison morphism `(F ⊗ Ω^i_{X/S})|_T ⟶ F_T ⊗ N` is locally surjective. -/
instance isLocallySurjective_tensorFormsAmbientUnit :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (tensorFormsAmbientUnit F c) :=
  @Presheaf.isLocallySurjective_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (isLocallySurjective_tensorFormsAmbient F c)
    (isLocallySurjective_tensorSheafUnit F (A := A) (N := N))

/-- The comparison morphism on sections, as an additive map out of the tensor product. -/
def tensorFormsAmbientUnitApp (V : A.obj.thickening.target.scheme.Opens) :
    F.val.obj (op (A.restrictOpen V)) ⊗[crysFormRing S (A.restrictOpen V)]
        (crysDifferentialForms S i).obj (op (A.restrictOpen V)) →+
      ((SheafOfModules.toSheaf _).obj (ambientTensor F N)).obj.obj (op V) :=
  ((tensorFormsAmbientUnit F c).app (op V)).hom

/-- The comparison morphism on a pure tensor, at the spelling of `tensorFormsAmbientUnitApp`. -/
theorem tensorFormsAmbientUnitApp_tmul (V : A.obj.thickening.target.scheme.Opens)
    (x : F.val.obj (op (A.restrictOpen V)))
    (ω : (crysDifferentialForms S i).obj (op (A.restrictOpen V))) :
    tensorFormsAmbientUnitApp F c V (restrTmul V x ω) =
      Stacks.PullbackTensorCoherence.tmul A.obj.thickening.target.scheme.toRingedSpace
        (crysAmbientSchemeModules F A) N (op V) x (c.toFun V ω) := rfl

/-- **Additive maps out of `F_T ⊗ N` agree on the image of the comparison as soon as they agree on
the images of pure tensors.** -/
theorem tensorFormsAmbientUnit_ext (V : A.obj.thickening.target.scheme.Opens)
    {G : AddCommGrpCat.{w}}
    (L R : ((SheafOfModules.toSheaf _).obj (ambientTensor F N)).obj.obj (op V) →+ G)
    (h : ∀ (x : F.val.obj (op (A.restrictOpen V)))
      (ω : (crysDifferentialForms S i).obj (op (A.restrictOpen V))),
      L (tensorFormsAmbientUnitApp F c V (restrTmul V x ω)) =
        R (tensorFormsAmbientUnitApp F c V (restrTmul V x ω)))
    (p : (tensorRestriction A F i).presheaf.obj (op V)) :
    L ((tensorFormsAmbientUnit F c).app (op V) p) = R ((tensorFormsAmbientUnit F c).app (op V) p) :=
  DFunLike.congr_fun (addMonoidHom_tensor_ext (f := L.comp (tensorFormsAmbientUnitApp F c V))
    (g := R.comp (tensorFormsAmbientUnitApp F c V)) h) p

/-- **Two compatible families of additive maps out of `F_T ⊗ N` into a Zariski sheaf, depending on
a parameter that restricts with the open, agree as soon as they agree on the images of pure tensors
of the presheaf `F ⊗ Ω^i_{X/S}`.** -/
theorem zariski_eq_of_tmul {Z : (A.obj.thickening.target.scheme.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u}}
    (hZ : Presheaf.IsSheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme) Z)
    {Ω : A.obj.thickening.target.scheme.Opens → Type*}
    (res : ∀ {V V' : A.obj.thickening.target.scheme.Opens}, V' ≤ V → Ω V → Ω V')
    (L R : ∀ V : A.obj.thickening.target.scheme.Opens, Ω V →
      ((SheafOfModules.toSheaf _).obj (ambientTensor F N)).obj.obj (op V) →+ Z.obj (op V))
    (hL : ∀ (V V' : A.obj.thickening.target.scheme.Opens) (h : V' ≤ V) (ω : Ω V)
      (z : ((SheafOfModules.toSheaf _).obj (ambientTensor F N)).obj.obj (op V)),
      Z.map (homOfLE h).op (L V ω z) = L V' (res h ω)
        (((SheafOfModules.toSheaf _).obj (ambientTensor F N)).obj.map (homOfLE h).op z))
    (hR : ∀ (V V' : A.obj.thickening.target.scheme.Opens) (h : V' ≤ V) (ω : Ω V)
      (z : ((SheafOfModules.toSheaf _).obj (ambientTensor F N)).obj.obj (op V)),
      Z.map (homOfLE h).op (R V ω z) = R V' (res h ω)
        (((SheafOfModules.toSheaf _).obj (ambientTensor F N)).obj.map (homOfLE h).op z))
    (he : ∀ (V : A.obj.thickening.target.scheme.Opens) (ω : Ω V)
      (x : F.val.obj (op (A.restrictOpen V)))
      (ω' : (crysDifferentialForms S i).obj (op (A.restrictOpen V))),
      L V ω (tensorFormsAmbientUnitApp F c V (restrTmul V x ω')) =
        R V ω (tensorFormsAmbientUnitApp F c V (restrTmul V x ω')))
    (V : A.obj.thickening.target.scheme.Opens) (ω : Ω V)
    (z : ((SheafOfModules.toSheaf _).obj (ambientTensor F N)).obj.obj (op V)) :
    L V ω z = R V ω z :=
  zariski_eq_of_generators.{u, u, u} (tensorFormsAmbientUnit F c) hZ res
    (fun V ω z ↦ L V ω z) (fun V ω z ↦ R V ω z) hL hR
    (fun V ω p ↦ tensorFormsAmbientUnit_ext F c V (L V ω) (R V ω) (he V ω) p) V ω z

/-- The comparison morphism on a pure tensor. -/
theorem tensorFormsAmbientUnit_app_tmul (W : A.obj.thickening.target.scheme.Opens)
    (x : F.val.obj (op (A.restrictOpen W)))
    (ω : (crysDifferentialForms S i).obj (op (A.restrictOpen W))) :
    (tensorFormsAmbientUnit F c).app (op W) (restrTmul W x ω) =
      Stacks.PullbackTensorCoherence.tmul A.obj.thickening.target.scheme.toRingedSpace
        (crysAmbientSchemeModules F A) N (op W) x (c.toFun W ω) := rfl

/-! ### The identification -/

/-- The Zariski sheaf `F_T ⊗ N` on `T`, read at the coefficient universe `u + 1`. -/
abbrev ambientTensorSheafULift (N : A.obj.thickening.target.scheme.Modules) :
    (A.obj.thickening.target.scheme.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  ((SheafOfModules.toSheaf _).obj (ambientTensor F N)).obj ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- The presheaf `F_T ⊗ N` at the coefficient universe `u + 1` is a Zariski sheaf. -/
theorem isSheaf_ambientTensorSheafULift (N : A.obj.thickening.target.scheme.Modules) :
    Presheaf.IsSheaf (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (ambientTensorSheafULift F N) :=
  ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
    ((SheafOfModules.toSheaf _).obj (ambientTensor F N))).property

/-- The comparison morphism at the coefficient universe `u + 1`. -/
def tensorFormsAmbientUnitULift :
    (CrystallineThickening.restrictOpenFunctor A).op ⋙ tensorDifferentialFormsPresheaf F i ⟶
      ambientTensorSheafULift F N :=
  Functor.whiskerRight (tensorFormsAmbientUnit F c) AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- The comparison morphism at the coefficient universe `u + 1` is locally injective. -/
instance isLocallyInjective_tensorFormsAmbientUnitULift :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (tensorFormsAmbientUnitULift F c) :=
  Presheaf.isLocallyInjective_whiskerRight_uliftFunctor _ _

/-- The comparison morphism at the coefficient universe `u + 1` is locally surjective. -/
instance isLocallySurjective_tensorFormsAmbientUnitULift :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      (tensorFormsAmbientUnitULift F c) :=
  Presheaf.isLocallySurjective_whiskerRight_uliftFunctor _ _

/-- **`(F ⊗_{𝒪_{X/S}} Ω^i_{X/S})_T ≅ F_T ⊗_{𝒪_T} N`**: the restriction to the ambient scheme of
`A` of the sheaf `F ⊗ Ω^i_{X/S}` on `Cris(X/S)` is the tensor product sheaf `F_T ⊗ N`, for every
comparison `c` of `Ω^i_{X/S}` with `N`.  No hypothesis on `F` is carried. -/
def tensorFormsAmbientIso :
    (CrystallineThickening.restrictOpenFunctor A).op ⋙ (tensorDifferentialFormsSheaf F i).obj ≅
      ambientTensorSheafULift F N :=
  haveI := isLocallyInjective_toSheafify (tensorDifferentialFormsPresheaf F i)
  haveI := isLocallySurjective_toSheafify (tensorDifferentialFormsPresheaf F i)
  CrystallineThickening.restrictOpenSheafifyIso A
    (CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i))
    (isSheaf_ambientTensorSheafULift F N) (tensorDifferentialFormsSheaf F i).property
    (tensorFormsAmbientUnitULift F c)

/-- **The identification is `x ⊗ ω ↦ x ⊗ ω`** on the image of the presheaf tensor product. -/
theorem tensorFormsAmbientIso_hom_app_toSheafify (W : A.obj.thickening.target.scheme.Opens)
    (x : F.val.obj (op (A.restrictOpen W)))
    (ω : (crysDifferentialForms S i).obj (op (A.restrictOpen W))) :
    (tensorFormsAmbientIso F c).hom.app (op W)
        ((CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i)).app
          (op (A.restrictOpen W))
            (ULift.up (restrTmul W x ω))) =
      ULift.up (Stacks.PullbackTensorCoherence.tmul A.obj.thickening.target.scheme.toRingedSpace
        (crysAmbientSchemeModules F A) N (op W) x (c.toFun W ω)) := by
  have := isLocallyInjective_toSheafify (tensorDifferentialFormsPresheaf F i)
  have := isLocallySurjective_toSheafify (tensorDifferentialFormsPresheaf F i)
  have h := CrystallineThickening.whiskerLeft_comp_restrictOpenSheafifyIso_hom A
    (CategoryTheory.toSheafify (smallTopology S) (tensorDifferentialFormsPresheaf F i))
    (isSheaf_ambientTensorSheafULift F N) (tensorDifferentialFormsSheaf F i).property
    (tensorFormsAmbientUnitULift F c)
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h (op W))
    (ULift.up (restrTmul W x ω))

end GlobalCrystallineSituation.SmallSite

end Crystalline

end
