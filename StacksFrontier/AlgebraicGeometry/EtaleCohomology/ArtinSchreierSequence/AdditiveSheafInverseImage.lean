module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantSequenceDatum
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqTranspose

/-!
# `𝐆_a` under inverse image, scalars, and the Artin–Schreier sequence

Let `g : Y ⟶ X` be a morphism of schemes. Pulling a global function back along the projection
`V ×_X Y ⟶ V` defines a morphism `𝐆_{a,X} ⟶ g_* 𝐆_{a,Y}` of abelian sheaves on `X_étale`, and
its adjoint transpose `g^{-1} 𝐆_{a,X} ⟶ 𝐆_{a,Y}`. This file records how that comparison
interacts with the structure carried by `𝐆_a`:

* multiplication by a global function `a` of `X` (`Stacks.ArtinSchreier.additiveSmul`) is carried
  to multiplication by its pullback to `Y`;
* the Frobenius `x ↦ x ^ p`, hence the Artin–Schreier map, is carried to the Frobenius;
* the inclusion `𝐙/p𝐙 ⟶ 𝐆_a` of the Artin–Schreier sequence is carried to the inclusion, through
  the canonical identification of the inverse image of a constant sheaf with the constant sheaf.

## Main definitions

* `Stacks.ArtinSchreier.additiveDirectImageComparison`: `𝐆_{a,X} ⟶ g_* 𝐆_{a,Y}`.
* `Stacks.ArtinSchreier.additiveInverseImageComparison`: `g^{-1} 𝐆_{a,X} ⟶ 𝐆_{a,Y}`.
* `Stacks.ArtinSchreier.additiveSmul`: multiplication by a global function on `𝐆_a`.

## Main results

* `Stacks.ArtinSchreier.inverseImage_additiveSmul_comp_additiveInverseImageComparison`,
  `Stacks.ArtinSchreier.inverseImage_artinSchreierMap_comp_additiveInverseImageComparison` and
  `Stacks.ArtinSchreier.inverseImage_zmodSheafHom_comp_additiveInverseImageComparison`: the three
  compatibilities above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.EtaleCohomology

universe u v

namespace Stacks.ArtinSchreier

/-! ### Multiplication by a global function -/

section Smul

variable (X : Scheme.{u})

/-- The pullback of a global function of `X` to an étale `X`-scheme `V`. -/
def etaleFunction {X : Scheme.{u}} (V : X.Etale) : Γ(X, ⊤) →+* Γ(V.left, ⊤) :=
  V.hom.appTop.hom

/-- Pulling a global function back to `V` and then along a morphism `W ⟶ V` of étale
`X`-schemes is pulling it back to `W`. -/
theorem appTop_etaleFunction {X : Scheme.{u}} {V W : X.Etale} (f : W ⟶ V) (a : Γ(X, ⊤)) :
    f.left.appTop.hom (etaleFunction V a) = etaleFunction W a := by
  change (V.hom.appTop ≫ f.left.appTop).hom a = W.hom.appTop.hom a
  rw [← Scheme.Hom.comp_appTop]
  exact congrArg (fun φ : W.left ⟶ X => φ.appTop.hom a)
    (MorphismProperty.Over.w f : f.left ≫ V.hom = W.hom)

/-- **Multiplication by a global function `a` of `X` on `𝐆_a`**: on sections over an étale
`X`-scheme `V` it multiplies by the pullback of `a` to `V`. -/
def additiveSmul (a : Γ(X, ⊤)) : additiveSheaf.{u, v} X ⟶ additiveSheaf.{u, v} X :=
  ⟨{ app V := AddCommGrpCat.ofHom
        (X := (additiveSheaf.{u, v} X).obj.obj V) (Y := (additiveSheaf.{u, v} X).obj.obj V)
        ((AddEquiv.ulift.symm.toAddMonoidHom.comp
          (AddMonoidHom.mulLeft (etaleFunction V.unop a))).comp
          AddEquiv.ulift.toAddMonoidHom)
     naturality V W f := by
      ext x
      obtain ⟨y, rfl⟩ := ofSection_surjective.{u, v} (U := V.unop) x
      change ofSection.{u, v} (U := W.unop) (etaleFunction W.unop a * f.unop.left.appTop.hom y) =
        ofSection.{u, v} (U := W.unop)
          (f.unop.left.appTop.hom (etaleFunction V.unop a * y))
      rw [map_mul, appTop_etaleFunction] }⟩

/-- Multiplication by `a` on sections. -/
@[simp]
theorem additiveSmul_app_ofSection (a : Γ(X, ⊤)) (V : X.Etale) (x : Γ(V.left, ⊤)) :
    (additiveSmul.{u, v} X a).hom.app (op V) (ofSection x) =
      ofSection (etaleFunction V a * x) :=
  rfl

/-- Morphisms out of `𝐆_a` agree if they agree on the image of every global function. -/
private theorem additiveSheaf_hom_ext {X : Scheme.{u}}
    {F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
    {f f' : additiveSheaf.{u, v} X ⟶ F}
    (h : ∀ (V : X.Etale) (x : Γ(V.left, ⊤)),
      f.hom.app (op V) (ofSection x) = f'.hom.app (op V) (ofSection x)) : f = f' := by
  ext V x
  obtain ⟨y, rfl⟩ := ofSection_surjective.{u, v} (U := V.unop) x
  exact h V.unop y

/-- Multiplication by a sum is the sum of the multiplications. -/
theorem additiveSmul_add (a b : Γ(X, ⊤)) :
    additiveSmul.{u, v} X (a + b) = additiveSmul.{u, v} X a + additiveSmul.{u, v} X b := by
  refine additiveSheaf_hom_ext fun V y => ?_
  change ofSection.{u, v} (U := V) (etaleFunction V (a + b) * y) =
    ofSection.{u, v} (U := V) (etaleFunction V a * y) +
      ofSection.{u, v} (U := V) (etaleFunction V b * y)
  rw [map_add, add_mul]
  rfl

/-- Multiplication by a product is the composite of the multiplications. -/
theorem additiveSmul_mul (a b : Γ(X, ⊤)) :
    additiveSmul.{u, v} X (a * b) = additiveSmul.{u, v} X b ≫ additiveSmul.{u, v} X a := by
  refine additiveSheaf_hom_ext fun V y => ?_
  change ofSection.{u, v} (U := V) (etaleFunction V (a * b) * y) =
    ofSection.{u, v} (U := V) (etaleFunction V a * (etaleFunction V b * y))
  rw [map_mul, mul_assoc]

/-- Multiplication by `1` is the identity. -/
theorem additiveSmul_one : additiveSmul.{u, v} X 1 = 𝟙 _ := by
  refine additiveSheaf_hom_ext fun V y => ?_
  change ofSection.{u, v} (U := V) (etaleFunction V 1 * y) =
    ofSection.{u, v} (U := V) y
  rw [map_one, one_mul]

end Smul

/-! ### The comparison along a morphism of schemes -/

section Comparison

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- **The comparison `𝐆_{a,X} ⟶ g_* 𝐆_{a,Y}`**: a global function on an étale `X`-scheme `V`
pulls back to a global function on `V ×_X Y`, which is a section of `g_* 𝐆_{a,Y}` over `V`. -/
def additiveDirectImageComparison :
    additiveSheaf.{u, v} X ⟶ (etaleAbelianDirectImage.{u, v} g).obj (additiveSheaf.{u, v} Y) :=
  ⟨Functor.whiskerRight (NatTrans.op (smallEtaleBaseChangeProjection g))
    (Scheme.Γ ⋙ additiveCoefficients.{u, v})⟩

/-- **On sections the comparison is pullback along `V ×_X Y ⟶ V`.** -/
@[simp]
theorem additiveDirectImageComparison_app_ofSection (V : X.Etale) (x : Γ(V.left, ⊤)) :
    (additiveDirectImageComparison.{u, v} g).hom.app (op V) (ofSection x) =
      ofSection (U := (smallEtaleBaseChange g).obj V) ((pullback.fst V.hom g).appTop.hom x) :=
  rfl

/-- **The comparison `g^{-1} 𝐆_{a,X} ⟶ 𝐆_{a,Y}`**, the adjoint transpose of
`Stacks.ArtinSchreier.additiveDirectImageComparison`. -/
def additiveInverseImageComparison :
    (etaleAbelianInverseImage.{u, v} g).obj (additiveSheaf.{u, v} X) ⟶ additiveSheaf.{u, v} Y :=
  ((etaleAbelianInverseImageDirectImageAdj.{u, v} g).homEquiv _ _).symm
    (additiveDirectImageComparison.{u, v} g)

/-- The transpose of the inverse-image comparison is the direct-image comparison. -/
theorem additiveInverseImageComparison_transpose :
    (etaleAbelianInverseImageDirectImageAdj.{u, v} g).homEquiv _ _
        (additiveInverseImageComparison.{u, v} g) =
      additiveDirectImageComparison.{u, v} g :=
  Equiv.apply_symm_apply _ _

/-- **Transport of a compatibility from the direct image to the inverse image.** If `m` on
`𝐆_{a,X}` and `m'` on `𝐆_{a,Y}` are intertwined by the direct-image comparison, they are
intertwined by the inverse-image comparison. -/
theorem inverseImage_map_comp_additiveInverseImageComparison
    {m : additiveSheaf.{u, v} X ⟶ additiveSheaf.{u, v} X}
    {m' : additiveSheaf.{u, v} Y ⟶ additiveSheaf.{u, v} Y}
    (h : m ≫ additiveDirectImageComparison.{u, v} g =
      additiveDirectImageComparison.{u, v} g ≫ (etaleAbelianDirectImage.{u, v} g).map m') :
    (etaleAbelianInverseImage.{u, v} g).map m ≫ additiveInverseImageComparison.{u, v} g =
      additiveInverseImageComparison.{u, v} g ≫ m' := by
  apply ((etaleAbelianInverseImageDirectImageAdj.{u, v} g).homEquiv _ _).injective
  rwa [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    additiveInverseImageComparison_transpose]

/-- Pulling a global function of `X` back to `V` and then to `V ×_X Y` is pulling its pullback
to `Y` back to `V ×_X Y`. -/
theorem appTop_fst_etaleFunction (V : X.Etale) (a : Γ(X, ⊤)) :
    (pullback.fst V.hom g).appTop.hom (etaleFunction V a) =
      etaleFunction ((smallEtaleBaseChange g).obj V) (g.appTop.hom a) := by
  change (V.hom.appTop ≫ (pullback.fst V.hom g).appTop).hom a =
    (g.appTop ≫ (pullback.snd V.hom g).appTop).hom a
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, pullback.condition]

/-- **The comparison carries multiplication by `a` to multiplication by its pullback.** -/
theorem additiveSmul_comp_additiveDirectImageComparison (a : Γ(X, ⊤)) :
    additiveSmul.{u, v} X a ≫ additiveDirectImageComparison.{u, v} g =
      additiveDirectImageComparison.{u, v} g ≫
        (etaleAbelianDirectImage.{u, v} g).map (additiveSmul.{u, v} Y (g.appTop.hom a)) := by
  refine additiveSheaf_hom_ext fun V y => ?_
  change ofSection.{u, v} (U := (smallEtaleBaseChange g).obj V)
      ((pullback.fst V.hom g).appTop.hom (etaleFunction V a * y)) =
    ofSection.{u, v} (U := (smallEtaleBaseChange g).obj V)
      ((id (etaleFunction ((smallEtaleBaseChange g).obj V) (g.appTop.hom a)) :
          Γ(pullback V.hom g, ⊤)) * (pullback.fst V.hom g).appTop.hom y)
  rw [map_mul, appTop_fst_etaleFunction]
  rfl

/-- **The inverse-image comparison carries multiplication by `a` to multiplication by its
pullback.** -/
theorem inverseImage_additiveSmul_comp_additiveInverseImageComparison (a : Γ(X, ⊤)) :
    (etaleAbelianInverseImage.{u, v} g).map (additiveSmul.{u, v} X a) ≫
        additiveInverseImageComparison.{u, v} g =
      additiveInverseImageComparison.{u, v} g ≫ additiveSmul.{u, v} Y (g.appTop.hom a) :=
  inverseImage_map_comp_additiveInverseImageComparison g
    (additiveSmul_comp_additiveDirectImageComparison g a)

/-- If the prime `p` vanishes on `X` it vanishes on `Y`. -/
theorem natCast_eq_zero_of_hom (g : Y ⟶ X) {p : ℕ} (hX : (p : Γ(X, ⊤)) = 0) : (p : Γ(Y, ⊤)) = 0 :=
  (map_natCast g.appTop.hom p).symm.trans ((congrArg g.appTop.hom hX).trans (map_zero _))

/-- **The comparison commutes with the Frobenius**: ring homomorphisms preserve `p`-th powers. -/
theorem frobeniusMap_comp_additiveDirectImageComparison {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) :
    frobeniusMap.{u, v} X hp hX ≫ additiveDirectImageComparison.{u, v} g =
      additiveDirectImageComparison.{u, v} g ≫
        (etaleAbelianDirectImage.{u, v} g).map
          (frobeniusMap.{u, v} Y hp (natCast_eq_zero_of_hom g hX)) := by
  refine additiveSheaf_hom_ext fun V y => ?_
  change ofSection.{u, v} (U := (smallEtaleBaseChange g).obj V)
      ((pullback.fst V.hom g).appTop.hom (y ^ p)) =
    ofSection.{u, v} (U := (smallEtaleBaseChange g).obj V)
      (((pullback.fst V.hom g).appTop.hom y) ^ p)
  rw [map_pow]

/-- **The comparison commutes with the Artin–Schreier map.** -/
theorem artinSchreierMap_comp_additiveDirectImageComparison {p : ℕ} (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) :
    artinSchreierMap.{u, v} X hp hX ≫ additiveDirectImageComparison.{u, v} g =
      additiveDirectImageComparison.{u, v} g ≫
        (etaleAbelianDirectImage.{u, v} g).map
          (artinSchreierMap.{u, v} Y hp (natCast_eq_zero_of_hom g hX)) := by
  rw [artinSchreierMap, artinSchreierMap, Functor.map_sub, CategoryTheory.Functor.map_id,
    Preadditive.sub_comp, Preadditive.comp_sub, frobeniusMap_comp_additiveDirectImageComparison,
    Category.id_comp, Category.comp_id]

/-- **The inverse-image comparison commutes with the Artin–Schreier map.** -/
theorem inverseImage_artinSchreierMap_comp_additiveInverseImageComparison {p : ℕ}
    (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) :
    (etaleAbelianInverseImage.{u, v} g).map (artinSchreierMap.{u, v} X hp hX) ≫
        additiveInverseImageComparison.{u, v} g =
      additiveInverseImageComparison.{u, v} g ≫
        artinSchreierMap.{u, v} Y hp (natCast_eq_zero_of_hom g hX) :=
  inverseImage_map_comp_additiveInverseImageComparison g
    (artinSchreierMap_comp_additiveDirectImageComparison g hp hX)

end Comparison

/-! ### The inclusion of `𝐙/p𝐙` -/

section Inclusion

/-- **A ring homomorphism carries the scalar of a residue class to the scalar of the same
residue class**: both sides are additive maps out of `𝐙/p𝐙` sending `1` to `1`. -/
theorem ringHom_constZModHom {X Y : Scheme.{u}} {p : ℕ} (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) (U : X.Etale) (U' : Y.Etale)
    (φ : Γ(U.left, ⊤) →+* Γ(U'.left, ⊤)) (m : ZMod p) :
    φ (constZModHom X hX U m) = constZModHom Y hY U' m := by
  have h := addMonoidHom_ext_zmod (φ.toAddMonoidHom.comp (constZModHom X hX U))
    (constZModHom Y hY U') (by simp [constZModHom_one])
  exact congrFun (congrArg (fun (F : ZMod p →+ Γ(U'.left, ⊤)) => (F : ZMod p → _)) h) m

/-- The transpose of the inclusion of `𝐙/p𝐙` in `𝐆_a` along the constant-sheaf adjunction at a
final object sends a residue class to its scalar. -/
theorem constantSheafAdj_homEquiv_zmodSheafHom (Z : Scheme.{u}) {p : ℕ}
    (hZ : (p : Γ(Z, ⊤)) = 0) {T : Z.Etale} (hT : IsTerminal T) :
    (constantSheafAdj Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} hT).homEquiv _ _
        (zmodSheafHom.{u, v} Z hZ) =
      (zmodPresheafHom.{u, v} Z hZ).app (op T) := by
  rw [Adjunction.homEquiv_unit]
  ext m
  change ((toSheafify Z.smallEtaleTopology
    ((Functor.const Z.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod p)))) ≫
      (zmodSheafHom.{u, v} Z hZ).hom).app (op T)) m = _
  exact congrArg (fun φ => (φ.app (op T)) m) (toSheafify_zmodSheafHom.{u, v} Z hZ)

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- **The inverse-image comparison carries the inclusion of `𝐙/p𝐙` to the inclusion of
`𝐙/p𝐙`**, through the canonical identification of the inverse image of a constant sheaf with
the constant sheaf. Both sides are maps out of the inverse image of a constant sheaf; after
transposing along the two adjunctions both send a residue class to its scalar. -/
theorem inverseImage_zmodSheafHom_comp_additiveInverseImageComparison {p : ℕ}
    (hX : (p : Γ(X, ⊤)) = 0) :
    (etaleAbelianInverseImage.{u, v} g).map (zmodSheafHom.{u, v} X hX) ≫
        additiveInverseImageComparison.{u, v} g =
      ((etaleAbelianInverseImageConstantIso.{u, v} g).app
        (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod p)))).hom ≫
        zmodSheafHom.{u, v} Y (natCast_eq_zero_of_hom g hX) := by
  let : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    (HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
      RingHom.Etale.containsIdentities :
        MorphismProperty.IsMultiplicative
          (@Etale : MorphismProperty Scheme.{u})).toContainsIdentities
  let T : X.Etale := MorphismProperty.Over.mk ⊤ (𝟙 X) (by infer_instance)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ _
  let hGT := hT.isTerminalObj (smallEtaleBaseChange g)
  let adj := etaleAbelianInverseImageDirectImageAdj.{u, v} g
  have hiso : etaleAbelianInverseImageConstantIso.{u, v} g =
      ((constantSheafAdj _ _ hT).comp adj).leftAdjointUniq (constantSheafAdj _ _ hGT) := rfl
  rw [← Iso.inv_comp_eq, hiso, Iso.app_inv]
  apply ((constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} hGT).homEquiv
    _ _).injective
  refine (Adjunction.homEquiv_leftAdjointUniq_inv_app_comp
    ((constantSheafAdj _ _ hT).comp adj) (constantSheafAdj _ _ hGT) _ _).trans ?_
  rw [Adjunction.comp_homEquiv, Equiv.trans_apply]
  change (constantSheafAdj _ _ hT).homEquiv _ _ (adj.homEquiv _ _ _) = _
  rw [Adjunction.homEquiv_naturality_left, additiveInverseImageComparison_transpose,
    Adjunction.homEquiv_naturality_right, constantSheafAdj_homEquiv_zmodSheafHom,
    constantSheafAdj_homEquiv_zmodSheafHom]
  ext m
  change ofSection.{u, v} (U := (smallEtaleBaseChange g).obj T)
      ((pullback.fst T.hom g).appTop.hom (constZModHom X hX T m.down)) =
    ofSection.{u, v} (U := (smallEtaleBaseChange g).obj T)
      (constZModHom Y (natCast_eq_zero_of_hom g hX) ((smallEtaleBaseChange g).obj T) m.down)
  exact congrArg ofSection (ringHom_constZModHom hX (natCast_eq_zero_of_hom g hX) T
    ((smallEtaleBaseChange g).obj T) (pullback.fst T.hom g).appTop.hom m.down)

end Inclusion

end Stacks.ArtinSchreier

end
