module

public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorAlongAComposite

/-!
# Tensor powers of pullbacks along composites

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of schemes and `L` an invertible `𝒪_Z`-module.
`AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso` identifies the pullback of a tensor
power of `L` with the tensor power of the pullback, `f^* (L ^⊗ n) ≅ (f^* L) ^⊗ n`. This file
proves that this identification is compatible with composition of morphisms and natural in the
module, and builds from it the **transfer** of an isomorphism `κ : a^* M ≅ b^* M` of two
pullbacks of an invertible module to the tensor powers, `a^* (M ^⊗ n) ≅ b^* (M ^⊗ n)`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.tensorPowerTransfer`: the transfer of `κ` to the `n`th
  tensor powers.

## Main results

* `AlgebraicGeometry.Scheme.Modules.pullbackTensorIso_comp`: the comparison of Stacks 01CD for
  `f ≫ g` is the comparison for `g`, then for `f`, then the composition law in each factor.
* `AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso_comp`: the same for the tensor
  powers.
* `AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso_naturality`: naturality in the
  module.
* `Stacks.SheafOfModules.Invertible.tensorPowerCongr_trans`, `…_refl` and `…_symm`: the tensor
  powers of isomorphisms are functorial.
* `AlgebraicGeometry.Scheme.Modules.tensorPowerTransfer_trans`, `…_refl` and
  `…_pullback`: transfers compose, the transfer of an identity is an identity, and the pullback
  of a transfer is the transfer of the pullback.

## Implementation notes

The statements mix `X.Modules` with the sheaves of modules over the structure sheaf that the
tensor powers are stated for, and the two are only definitionally equal; the goals are not
type-correct at the transparency `rw` and `simp` check motives at. Every identity is therefore
proved in free objects first (the lemmas with suffix `_aux`, where those tactics work), and the
statements about schemes are instances of them obtained by `exact`.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Invertible

universe u v w

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : CategoryTheory.Presheaf.IsSheaf J
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {L M N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)}
  [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible O hO M]
  [AlgebraicGeometry.SheafOfModules.IsInvertible O hO N]

/-- The successor step of `tensorPowerCongr_trans`, in free objects. -/
theorem tensorPowerCongr_trans_aux {D : Type*} [Category D] (F : D ⥤ D ⥤ D)
    {P Q R Ln Mn Nn L' M' N' : D} (s : (F.obj Ln).obj L' ≅ P) (s₂ : (F.obj Mn).obj M' ≅ Q)
    (s₃ : (F.obj Nn).obj N' ≅ R) (c : Ln ≅ Mn) (c' : Mn ≅ Nn) (c'' : Ln ≅ Nn) (e : L' ≅ M')
    (e' : M' ≅ N') (h : c'' = c ≪≫ c') :
    s.symm ≪≫ (F.flip.obj L').mapIso c'' ≪≫ (F.obj Nn).mapIso (e ≪≫ e') ≪≫ s₃ =
      (s.symm ≪≫ (F.flip.obj L').mapIso c ≪≫ (F.obj Mn).mapIso e ≪≫ s₂) ≪≫
        (s₂.symm ≪≫ (F.flip.obj M').mapIso c' ≪≫ (F.obj Nn).mapIso e' ≪≫ s₃) := by
  subst h
  refine Iso.ext ?_
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Functor.flip_obj_map, NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← reassoc_of% ((F.map c'.hom).naturality e.hom)]

/-- **The tensor powers of a composite isomorphism compose.** -/
theorem tensorPowerCongr_trans (e : L ≅ M) (e' : M ≅ N) : ∀ n : ℕ,
    tensorPowerCongr O hO L N (e ≪≫ e') n =
      tensorPowerCongr O hO L M e n ≪≫ tensorPowerCongr O hO M N e' n
  | 0 => (Iso.refl_trans _).symm
  | n + 1 => tensorPowerCongr_trans_aux _ _ _ _ _ _ _ _ _ (tensorPowerCongr_trans e e' n)

/-- The successor step of `tensorPowerCongr_refl`, in free objects. -/
theorem tensorPowerCongr_refl_aux {D : Type*} [Category D] (F : D ⥤ D ⥤ D) {P Ln L' : D}
    (s : (F.obj Ln).obj L' ≅ P) (c : Ln ≅ Ln) (h : c = Iso.refl Ln) :
    s.symm ≪≫ (F.flip.obj L').mapIso c ≪≫ (F.obj Ln).mapIso (Iso.refl L') ≪≫ s = Iso.refl P := by
  subst h
  refine Iso.ext ?_
  simp

/-- **The tensor powers of an identity are identities.** -/
theorem tensorPowerCongr_refl : ∀ n : ℕ,
    tensorPowerCongr O hO L L (Iso.refl L) n = Iso.refl _
  | 0 => rfl
  | n + 1 => tensorPowerCongr_refl_aux _ _ _ (tensorPowerCongr_refl n)

/-- **The tensor powers of an inverse are the inverses.** -/
theorem tensorPowerCongr_symm (e : L ≅ M) (n : ℕ) :
    tensorPowerCongr O hO M L e.symm n = (tensorPowerCongr O hO L M e n).symm := by
  have h := (tensorPowerCongr_trans O hO e e.symm n).symm.trans
    ((congrArg (fun k => tensorPowerCongr O hO L L k n) e.self_symm_id).trans
      (tensorPowerCongr_refl O hO n))
  exact Iso.ext (Iso.inv_ext' (congrArg Iso.hom h))


end Stacks.SheafOfModules.Invertible

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The tensor bifunctor of sheaves of modules on a scheme, at the spelling of
`AlgebraicGeometry.Scheme.Modules.pullbackTensorPowerIso`. -/
abbrev tensorBifunctor (X : Scheme.{u}) :=
  Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨X.sheaf.obj, Presheaf.isSheaf_of_isSheaf_comp _ X.sheaf.obj (forget₂ CommRingCat RingCat)
      X.ringCatSheaf.property⟩

/-- The comparison `(f ≫ g)^* (A ⊗ B) ≅ (f ≫ g)^* A ⊗ (f ≫ g)^* B`, preceded by the composition
law `f^* g^* ≅ (f ≫ g)^*`, is the comparison for `g` pulled back along `f`, then the comparison for
`f`, then the composition law in each tensor factor. -/
theorem pullbackTensorIso_comp (A B : Z.Modules) :
    (Scheme.Modules.pullbackComp f g).hom.app (((tensorBifunctor Z).obj A).obj B) ≫
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso (f ≫ g) A B).hom =
      (Scheme.Modules.pullback f).map
          (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso g A B).hom ≫
        (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f _ _).hom ≫
        ((tensorBifunctor X).map ((Scheme.Modules.pullbackComp f g).hom.app A)).app _ ≫
        ((tensorBifunctor X).obj _).map ((Scheme.Modules.pullbackComp f g).hom.app B) :=
  Stacks.PullbackTensorComposition.comparison_comp f.toLRSHom.toShHom g.toLRSHom.toShHom A B

/-! ### Two identities in free objects -/

section Generic

variable {C D : Type*} [Category C] [Category D]

/-- The shape of the successor step: the cancellation of the two successor comparisons met in
the middle, leaving the core identity `h`. -/
theorem pullbackTensorPowerIso_comp_aux_succ (G : D ⥤ C) {a₀ a₁ a₂ c₁ c₂ c₃ c₄ c₅ c₆ : C}
    {b₀ b₁ b₂ b₃ b₄ : D} (κ : a₀ ⟶ G.obj b₀) (e₁ : b₀ ≅ b₁) (e₂ : b₁ ≅ b₂) (e₃ : b₂ ≅ b₃)
    (e₄ : b₃ ≅ b₄) (e₆ : G.obj b₃ ≅ c₁) (e₇ : c₁ ≅ c₂) (e₈ : c₂ ≅ c₃) (e₉ : c₂ ≅ c₄)
    (e₁₀ : c₄ ≅ c₅) (e₁₁ : c₅ ≅ c₆) (e₁₂ : a₀ ≅ a₁) (e₁₃ : a₁ ≅ a₂) (e₁₄ : a₂ ≅ c₅)
    (h : κ ≫ G.map e₁.hom ≫ G.map e₂.hom ≫ G.map e₃.hom ≫ e₆.hom ≫ e₇.hom ≫ e₉.hom ≫ e₁₀.hom =
      e₁₂.hom ≫ e₁₃.hom ≫ e₁₄.hom) :
    κ ≫ G.map (e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄).hom ≫ (G.mapIso e₄.symm ≪≫ e₆ ≪≫ e₇ ≪≫ e₈).hom ≫
        (e₈.symm ≪≫ e₉ ≪≫ e₁₀ ≪≫ e₁₁).hom =
      (e₁₂ ≪≫ e₁₃ ≪≫ e₁₄ ≪≫ e₁₁).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_map_assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% h]

/-- The core identity of the successor step, in free objects: naturality of the composition law,
its compatibility with the tensor comparison, naturality of the tensor comparison in its first
variable and the induction hypothesis combine through the interchange law of the bifunctor. -/
theorem pullbackTensorPowerIso_comp_aux_core (G : D ⥤ C) (T : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    {a₀ a₁ : C} {b₀ b₁ FLn FLn' FL : D} {HLn HL Q R : C}
    (κ : a₀ ⟶ G.obj b₀) (e₁ : b₀ ≅ b₁) (e₂ : b₁ ≅ (TD.obj FLn).obj FL) (Pg : FLn ≅ FLn')
    (Tf : G.obj ((TD.obj FLn').obj FL) ≅ (T.obj (G.obj FLn')).obj (G.obj FL))
    (Tf' : G.obj ((TD.obj FLn).obj FL) ≅ (T.obj (G.obj FLn)).obj (G.obj FL))
    (Pf : G.obj FLn' ≅ Q) (Cn : Q ≅ R) (c : G.obj FL ≅ HL)
    (e₁₂ : a₀ ≅ a₁) (Tgf : a₁ ≅ (T.obj HLn).obj HL) (Pgf : HLn ≅ R)
    (κ' : a₁ ⟶ G.obj b₁) (κn : HLn ⟶ G.obj FLn) (κL : HL ⟶ G.obj FL)
    (N1 : κ ≫ G.map e₁.hom = e₁₂.hom ≫ κ')
    (B : κ' ≫ G.map e₂.hom ≫ Tf'.hom =
      Tgf.hom ≫ (T.map κn).app HL ≫ (T.obj (G.obj FLn)).map κL)
    (N2 : G.map ((TD.flip.obj FL).mapIso Pg).hom ≫ Tf.hom =
      Tf'.hom ≫ (T.map (G.map Pg.hom)).app (G.obj FL))
    (IH : κn ≫ G.map Pg.hom ≫ Pf.hom ≫ Cn.hom = Pgf.hom)
    (H1 : κL ≫ c.hom = 𝟙 _) :
    κ ≫ G.map e₁.hom ≫ G.map e₂.hom ≫ G.map ((TD.flip.obj FL).mapIso Pg).hom ≫ Tf.hom ≫
        ((T.flip.obj (G.obj FL)).mapIso Pf).hom ≫ ((T.flip.obj (G.obj FL)).mapIso Cn).hom ≫
        ((T.obj R).mapIso c).hom =
      e₁₂.hom ≫ Tgf.hom ≫ ((T.flip.obj HL).mapIso Pgf).hom := by
  rw [reassoc_of% N1, reassoc_of% N2, reassoc_of% B]
  simp only [Functor.flip_obj_map, Functor.mapIso_hom]
  have nat : ∀ {A A' : C} (u : A ⟶ A'),
      (T.obj A).map κL ≫ (T.map u).app (G.obj FL) = (T.map u).app HL ≫ (T.obj A').map κL :=
    fun u => (T.map u).naturality κL
  rw [reassoc_of% nat, reassoc_of% nat, reassoc_of% nat, ← Functor.map_comp, H1, ← IH]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Functor.map_comp,
    NatTrans.comp_app]

/-- The inverse form of a compatibility of a comparison with an isomorphism of tensor
products. -/
theorem pullbackTensorPowerIso_comp_aux_inv (T : C ⥤ C ⥤ C) {P₁ P₂ Q : C} {A₁ A₂ B₁ B₂ : C}
    (x : P₁ ≅ P₂) (t : P₂ ⟶ (T.obj A₂).obj B₂) (y : P₁ ⟶ Q) (z : Q ⟶ (T.obj A₁).obj B₁)
    (u : A₁ ≅ A₂) (v : B₁ ≅ B₂)
    (h : x.hom ≫ t = y ≫ z ≫ (T.map u.hom).app B₁ ≫ (T.obj A₂).map v.hom) :
    x.inv ≫ y ≫ z = t ≫ (T.map u.inv).app B₂ ≫ (T.obj A₁).map v.inv := by
  rw [← cancel_epi x.hom, Iso.hom_inv_id_assoc, reassoc_of% h]
  have nat := (T.map u.inv).naturality v.hom
  have h1 : (T.map u.hom).app B₁ ≫ (T.map u.inv).app B₁ = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← T.map_comp, u.hom_inv_id, T.map_id, NatTrans.id_app]
  rw [reassoc_of% nat, reassoc_of% h1, Iso.hom_inv_id_map, Category.comp_id]

/-- Naturality of a comparison of bifunctors in the first variable, from its naturality as a
transformation of the uncurried bifunctors. -/
theorem pullbackTensorPowerIso_comp_aux_nat (G : D ⥤ C) (T : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    {A A' B : D} (u : A ≅ A') (t : G.obj ((TD.obj A).obj B) ⟶ (T.obj (G.obj A)).obj (G.obj B))
    (t' : G.obj ((TD.obj A').obj B) ⟶ (T.obj (G.obj A')).obj (G.obj B))
    (h : G.map ((Functor.uncurry.obj TD).map ((u.hom, 𝟙 B) : (A, B) ⟶ (A', B))) ≫ t' =
      t ≫ (Functor.uncurry.obj T).map
        ((G.map u.hom, G.map (𝟙 B)) : (G.obj A, G.obj B) ⟶ (G.obj A', G.obj B))) :
    G.map ((TD.flip.obj B).mapIso u).hom ≫ t' = t ≫ (T.map (G.map u.hom)).app (G.obj B) := by
  simpa using h

/-- The successor step of the naturality of `pullbackTensorPowerIso` in the module, in free
objects. -/
theorem pullbackTensorPowerIso_naturality_aux (G : D ⥤ C) (T : C ⥤ C ⥤ C) (TD : D ⥤ D ⥤ D)
    {Ln Ln' L L' P P' : D} {Qn Qn' Q₁ R : C}
    (s : (TD.obj Ln).obj L ≅ P) (s' : (TD.obj Ln').obj L' ≅ P') (cn : Ln ≅ Ln') (e : L ≅ L')
    (Tt : G.obj ((TD.obj Ln).obj L) ≅ (T.obj (G.obj Ln)).obj (G.obj L))
    (Tt' : G.obj ((TD.obj Ln').obj L') ≅ (T.obj (G.obj Ln')).obj (G.obj L'))
    (Pn : G.obj Ln ≅ Qn) (Pn' : G.obj Ln' ≅ Qn')
    (s₁ : (T.obj Qn).obj (G.obj L) ≅ Q₁) (s'' : (T.obj Qn').obj (G.obj L') ≅ R)
    (cX : Qn ≅ Qn')
    (IH : G.mapIso cn ≪≫ Pn' = Pn ≪≫ cX)
    (Nat : G.map ((Functor.uncurry.obj TD).map ((cn.hom, e.hom) : (Ln, L) ⟶ (Ln', L'))) ≫
        Tt'.hom = Tt.hom ≫ (Functor.uncurry.obj T).map
          ((G.map cn.hom, G.map e.hom) : (G.obj Ln, G.obj L) ⟶ (G.obj Ln', G.obj L'))) :
    G.mapIso (s.symm ≪≫ (TD.flip.obj L).mapIso cn ≪≫ (TD.obj Ln').mapIso e ≪≫ s') ≪≫
        (G.mapIso s'.symm ≪≫ Tt' ≪≫ (T.flip.obj (G.obj L')).mapIso Pn' ≪≫ s'') =
      (G.mapIso s.symm ≪≫ Tt ≪≫ (T.flip.obj (G.obj L)).mapIso Pn ≪≫ s₁) ≪≫
        (s₁.symm ≪≫ (T.flip.obj (G.obj L)).mapIso cX ≪≫ (T.obj Qn').mapIso (G.mapIso e) ≪≫
          s'') := by
  have IH' : G.map cn.hom ≫ Pn'.hom = Pn.hom ≫ cX.hom := congrArg Iso.hom IH
  refine Iso.ext ?_
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Functor.flip_obj_map, Category.assoc, Iso.hom_inv_id_map_assoc, Iso.hom_inv_id_assoc,
    cancel_epi]
  simp only [Functor.uncurry_obj_map, Functor.map_comp, Category.assoc] at Nat
  rw [reassoc_of% Nat]
  simp only [cancel_epi]
  rw [reassoc_of% ((T.map Pn'.hom).naturality (G.map e.hom)), ← NatTrans.comp_app_assoc,
    ← T.map_comp, IH', T.map_comp, NatTrans.comp_app_assoc]

/-- The pullback of a transfer of tensor powers, in free objects. -/
theorem tensorPowerTransfer_pullback_aux (G : D ⥤ C) {P₀ P₁ Sa Sb Ta Tb : C}
    {Pa₀ Pb₀ Qa Qb : D} (xa : P₀ ≅ G.obj Pa₀) (xb : P₁ ≅ G.obj Pb₀) (Pa : Pa₀ ≅ Qa)
    (Ck : Qa ≅ Qb) (Pb : Pb₀ ≅ Qb) (Ra : G.obj Qa ≅ Sa) (Rb : G.obj Qb ≅ Sb) (ca : Sa ≅ Ta)
    (cb : Sb ≅ Tb) (cg : Sa ≅ Sb) (Qa' : P₀ ≅ Ta) (Qb' : P₁ ≅ Tb) (tot : Ta ≅ Tb)
    (Ha : xa.hom ≫ G.map Pa.hom ≫ Ra.hom ≫ ca.hom = Qa'.hom)
    (Hb : xb.hom ≫ G.map Pb.hom ≫ Rb.hom ≫ cb.hom = Qb'.hom)
    (Nat : G.mapIso Ck ≪≫ Rb = Ra ≪≫ cg) (Htot : tot = ca.symm ≪≫ cg ≪≫ cb) :
    xa.hom ≫ G.map (Pa ≪≫ Ck ≪≫ Pb.symm).hom ≫ xb.inv = (Qa' ≪≫ tot ≪≫ Qb'.symm).hom := by
  subst Htot
  have Nat' : G.map Ck.hom ≫ Rb.hom = Ra.hom ≫ cg.hom := congrArg Iso.hom Nat
  rw [← cancel_mono Qb'.hom]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [← Hb, Iso.inv_hom_id_assoc, Iso.inv_hom_id_map_assoc, reassoc_of% Nat', ← Ha]
  simp

/-- Conjugates compose, in free objects. -/
theorem conj_trans_aux {P Q R P' Q' R' : C} (x : P ≅ P') (y : Q ≅ Q') (z : R ≅ R')
    (e : P' ≅ Q') (e' : Q' ≅ R') (e'' : P' ≅ R') (h : e'' = e ≪≫ e') :
    (x ≪≫ e ≪≫ y.symm) ≪≫ (y ≪≫ e' ≪≫ z.symm) = x ≪≫ e'' ≪≫ z.symm := by
  subst h; simp

/-- The conjugate of an identity is an identity, in free objects. -/
theorem conj_refl_aux {P P' : C} (x : P ≅ P') (e : P' ≅ P') (h : e = Iso.refl P') :
    x ≪≫ e ≪≫ x.symm = Iso.refl P := by
  subst h; simp

end Generic

/-- **Naturality of `pullbackTensorPowerIso` in the module.** -/
theorem pullbackTensorPowerIso_naturality {L L' : Y.Modules}
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L']
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback f).obj L)]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback f).obj L')]
    (e : L ≅ L') : ∀ n : ℕ,
    (Scheme.Modules.pullback f).mapIso
        (tensorPowerCongr Y.toRingedSpace.presheaf (structureSheafRing Y.toRingedSpace).property
          L L' e n) ≪≫ pullbackTensorPowerIso f L' n =
      pullbackTensorPowerIso f L n ≪≫
        tensorPowerCongr X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property
          ((Scheme.Modules.pullback f).obj L) ((Scheme.Modules.pullback f).obj L')
          ((Scheme.Modules.pullback f).mapIso e) n
  | 0 => Iso.ext ((congrArg (· ≫ _) (CategoryTheory.Functor.map_id _ _)).trans
      ((Category.id_comp _).trans (Category.comp_id _).symm))
  | n + 1 => pullbackTensorPowerIso_naturality_aux (Scheme.Modules.pullback f) _ _ _ _ _ e _ _
      _ _ _ _ _ (pullbackTensorPowerIso_naturality e n)
      ((Stacks.RingedSpace.comparisonNatTrans f.toLRSHom.toShHom).naturality _)

variable (L : Z.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible Z.toRingedSpace.presheaf
    (structureSheafRing Z.toRingedSpace).property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
    (structureSheafRing Y.toRingedSpace).property ((Scheme.Modules.pullback g).obj L)]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property
      ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj L))]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property ((Scheme.Modules.pullback (f ≫ g)).obj L)]

/-- The identification `(f ≫ g)^* (L ^⊗ n) ≅ ((f ≫ g)^* L) ^⊗ n` is the inverse composition law,
then the identification for `g` pulled back along `f`, then the identification for `f`, then the
`n`th tensor power of the composition law `f^* g^* L ≅ (f ≫ g)^* L`. -/
theorem pullbackTensorPowerIso_comp : ∀ n : ℕ,
    (Scheme.Modules.pullbackComp f g).inv.app
        (tensorPower Z.toRingedSpace.presheaf (structureSheafRing Z.toRingedSpace).property L
          (n : ℤ)) ≫
      (Scheme.Modules.pullback f).map (pullbackTensorPowerIso g L n).hom ≫
      (pullbackTensorPowerIso f ((Scheme.Modules.pullback g).obj L) n).hom ≫
      (tensorPowerCongr X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property
        ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj L))
        ((Scheme.Modules.pullback (f ≫ g)).obj L) ((Scheme.Modules.pullbackComp f g).app L)
        n).hom =
      (pullbackTensorPowerIso (f ≫ g) L n).hom
  | 0 => Eq.trans (congrArg (fun k => _ ≫ _ ≫ k) (Category.comp_id _))
      (pullbackUnitIso_comp f g)
  | n + 1 => by
    refine pullbackTensorPowerIso_comp_aux_succ (Scheme.Modules.pullback f)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_
    refine pullbackTensorPowerIso_comp_aux_core (Scheme.Modules.pullback f) _ _
      (Tf' := Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f
        ((Scheme.Modules.pullback g).obj (tensorPower Z.toRingedSpace.presheaf
          (structureSheafRing Z.toRingedSpace).property L (n : ℤ)))
        ((Scheme.Modules.pullback g).obj L))
      (κ' := (Scheme.Modules.pullbackComp f g).inv.app _)
      (κn := (Scheme.Modules.pullbackComp f g).inv.app (tensorPower Z.toRingedSpace.presheaf
          (structureSheafRing Z.toRingedSpace).property L (n : ℤ)))
      (κL := (Scheme.Modules.pullbackComp f g).inv.app L)
      _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ (pullbackTensorPowerIso_comp n)
      ((Scheme.Modules.pullbackComp f g).inv_hom_id_app L)
    · exact ((Scheme.Modules.pullbackComp f g).inv.naturality _).symm
    · exact pullbackTensorPowerIso_comp_aux_inv _ ((Scheme.Modules.pullbackComp f g).app _) _ _ _
        ((Scheme.Modules.pullbackComp f g).app _) ((Scheme.Modules.pullbackComp f g).app _)
        (pullbackTensorIso_comp f g _ _)
    · exact pullbackTensorPowerIso_comp_aux_nat _ _ _ _ _ _
        ((Stacks.RingedSpace.comparisonNatTrans f.toLRSHom.toShHom).naturality _)

/-! ### Transfers of tensor powers -/

section Transfer

variable {T T' : Scheme.{u}} (a b c : T ⟶ X) (M : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property M]
  [AlgebraicGeometry.SheafOfModules.IsInvertible T.toRingedSpace.presheaf
    (structureSheafRing T.toRingedSpace).property ((Scheme.Modules.pullback a).obj M)]
  [AlgebraicGeometry.SheafOfModules.IsInvertible T.toRingedSpace.presheaf
    (structureSheafRing T.toRingedSpace).property ((Scheme.Modules.pullback b).obj M)]
  [AlgebraicGeometry.SheafOfModules.IsInvertible T.toRingedSpace.presheaf
    (structureSheafRing T.toRingedSpace).property ((Scheme.Modules.pullback c).obj M)]

/-- **The transfer of an isomorphism of pullbacks of an invertible module to its tensor
powers.** An isomorphism `κ : a^* M ≅ b^* M` gives `a^* (M ^⊗ n) ≅ b^* (M ^⊗ n)`, through the
identifications of the pullback of a power with the power of the pullback. -/
def tensorPowerTransfer (κ : (Scheme.Modules.pullback a).obj M ≅ (Scheme.Modules.pullback b).obj M)
    (n : ℕ) :
    (Scheme.Modules.pullback a).obj
        (tensorPower X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property M
          (n : ℤ)) ≅
      (Scheme.Modules.pullback b).obj
        (tensorPower X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property M
          (n : ℤ)) :=
  pullbackTensorPowerIso a M n ≪≫
    tensorPowerCongr T.toRingedSpace.presheaf (structureSheafRing T.toRingedSpace).property
      ((Scheme.Modules.pullback a).obj M) ((Scheme.Modules.pullback b).obj M) κ n ≪≫
    (pullbackTensorPowerIso b M n).symm

/-- Transfers compose. -/
theorem tensorPowerTransfer_trans
    (κ : (Scheme.Modules.pullback a).obj M ≅ (Scheme.Modules.pullback b).obj M)
    (κ' : (Scheme.Modules.pullback b).obj M ≅ (Scheme.Modules.pullback c).obj M) (n : ℕ) :
    tensorPowerTransfer a b M κ n ≪≫ tensorPowerTransfer b c M κ' n =
      tensorPowerTransfer a c M (κ ≪≫ κ') n :=
  conj_trans_aux _ _ _ _ _ _ (tensorPowerCongr_trans T.toRingedSpace.presheaf
    (structureSheafRing T.toRingedSpace).property κ κ' n)

/-- The transfer of an identity is the identity. -/
theorem tensorPowerTransfer_refl (n : ℕ) :
    tensorPowerTransfer a a M (Iso.refl _) n = Iso.refl _ :=
  conj_refl_aux _ _ (tensorPowerCongr_refl T.toRingedSpace.presheaf
    (structureSheafRing T.toRingedSpace).property (L := (Scheme.Modules.pullback a).obj M) n)

/-- **The pullback of a transfer is the transfer of the pullback.** Pulling back the transfer of
`κ` along `g` and reading it through the composition comparisons gives the transfer of the
pullback of `κ`. -/
theorem tensorPowerTransfer_pullback (g : T' ⟶ T)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T'.toRingedSpace.presheaf
      (structureSheafRing T'.toRingedSpace).property
        ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback a).obj M))]
    [AlgebraicGeometry.SheafOfModules.IsInvertible T'.toRingedSpace.presheaf
      (structureSheafRing T'.toRingedSpace).property
        ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback b).obj M))]
    [AlgebraicGeometry.SheafOfModules.IsInvertible T'.toRingedSpace.presheaf
      (structureSheafRing T'.toRingedSpace).property ((Scheme.Modules.pullback (g ≫ a)).obj M)]
    [AlgebraicGeometry.SheafOfModules.IsInvertible T'.toRingedSpace.presheaf
      (structureSheafRing T'.toRingedSpace).property ((Scheme.Modules.pullback (g ≫ b)).obj M)]
    (κ : (Scheme.Modules.pullback a).obj M ≅ (Scheme.Modules.pullback b).obj M) (n : ℕ) :
    (Scheme.Modules.pullbackComp g a).inv.app
        (tensorPower X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property M
          (n : ℤ)) ≫
      (Scheme.Modules.pullback g).map (tensorPowerTransfer a b M κ n).hom ≫
      (Scheme.Modules.pullbackComp g b).hom.app
        (tensorPower X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property M
          (n : ℤ)) =
      (tensorPowerTransfer (g ≫ a) (g ≫ b) M
        ((Scheme.Modules.pullbackComp g a).symm.app M ≪≫ (Scheme.Modules.pullback g).mapIso κ ≪≫
          (Scheme.Modules.pullbackComp g b).app M) n).hom := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible T'.toRingedSpace.presheaf
      (structureSheafRing T'.toRingedSpace).property
        ((Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback g).obj M) :=
    inferInstanceAs (AlgebraicGeometry.SheafOfModules.IsInvertible T'.toRingedSpace.presheaf
      (structureSheafRing T'.toRingedSpace).property
        ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback a).obj M)))
  exact tensorPowerTransfer_pullback_aux (Scheme.Modules.pullback g)
    ((Scheme.Modules.pullbackComp g a).app _).symm ((Scheme.Modules.pullbackComp g b).app _).symm
    _ _ _ _ _ _ _ _ _ _ _
    (pullbackTensorPowerIso_comp g a M n) (pullbackTensorPowerIso_comp g b M n)
    (pullbackTensorPowerIso_naturality g κ n)
    ((tensorPowerCongr_trans T'.toRingedSpace.presheaf
      (structureSheafRing T'.toRingedSpace).property
      ((Scheme.Modules.pullbackComp g a).app M).symm
      ((Scheme.Modules.pullback g).mapIso κ ≪≫ (Scheme.Modules.pullbackComp g b).app M) n).trans
      (congrArg₂ (· ≪≫ ·)
        (tensorPowerCongr_symm T'.toRingedSpace.presheaf
          (structureSheafRing T'.toRingedSpace).property
          ((Scheme.Modules.pullbackComp g a).app M) n)
        (tensorPowerCongr_trans T'.toRingedSpace.presheaf
          (structureSheafRing T'.toRingedSpace).property
          ((Scheme.Modules.pullback g).mapIso κ) ((Scheme.Modules.pullbackComp g b).app M) n)))

end Transfer

end AlgebraicGeometry.Scheme.Modules
