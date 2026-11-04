module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.AdditiveSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.BaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.Exactness
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyOverAnObject
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing

/-!
# Maps out of `j_! j^{-1} ℤ` and their `Ext¹` into `𝐆_a`

Let `j : W ⟶ X` be the inclusion of an open subscheme and `ℤ_X` the constant sheaf on `X_étale`.
The sheaf `j_! j^{-1} ℤ_X` is the term attached to `W` in the Mayer–Vietoris sequence of a cover
of `X` by two opens (`Stacks.EtaleCohomology.shortExact_coverShortComplex`). This file records
the two facts about it that the Mayer–Vietoris computation of `H¹(X, 𝐆_a)` uses:

* morphisms `j_! j^{-1} ℤ_X ⟶ H` are the sections of `H` over `W`, additively and naturally in
  `H` (`Stacks.ArtinSchreier.extensionByZeroOfRestrictionHomAddEquiv`);
* for a morphism `g : Y ⟶ X` such that `W ×_X Y` is affine,
  `Ext¹(g^{-1} j_! j^{-1} ℤ_X, 𝐆_{a,Y}) = 0`: by Tag 03S6 the sheaf is `j'_! ℤ` for the open
  `j' : W ×_X Y ⟶ Y`, so the group is `H¹(W ×_X Y, 𝐆_a)`, which vanishes on an affine scheme
  (`Stacks.ArtinSchreier.subsingleton_ext_one_inverseImage_extensionByZeroOfRestriction`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.EtaleCohomology

universe w u

namespace Stacks.ArtinSchreier

/-- The constant sheaf `ℤ` on the small étale site of a scheme, the source of étale cohomology. -/
abbrev etaleConstantInt (S : Scheme.{u}) : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))

/-- **Restricting a constant sheaf along an étale morphism gives the constant sheaf**: restriction
is the inverse image (`Stacks.EtaleCohomology.etaleAbelianInverseImageRestrictionIso`), which
preserves constant sheaves. -/
def etaleRestrictionConstantIso {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
    (M : AddCommGrpCat.{u + 1}) :
    (etaleRestriction.{u, 0} j).obj
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M) ≅
      (constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M :=
  ((etaleAbelianInverseImageRestrictionIso.{u, 0} j).app _).symm ≪≫
    (etaleAbelianInverseImageConstantIso.{u, 0} j).app M

/-- **Restricting `𝐆_a` along an étale morphism `j : U ⟶ X` gives `𝐆_a` of `U`**: both have the
global functions of an étale `U`-scheme as sections. -/
def etaleRestrictionAdditiveSheafIso {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    (etaleRestriction.{u, 0} j).obj (additiveSheaf.{u, u + 1} X) ≅ additiveSheaf.{u, u + 1} U :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl))

/-- `Ext` groups between isomorphic objects are isomorphic. -/
def extIsoCongr {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C] {A A' B B' : C}
    (eA : A ≅ A') (eB : B ≅ B') (n : ℕ) : Ext.{w} A B n ≃+ Ext.{w} A' B' n :=
  ((((extFunctor.{w} n).mapIso eA.symm.op).app B) ≪≫
    ((extFunctor.{w} n).obj (op A')).mapIso eB).addCommGroupIsoToAddEquiv

/-! ### Vanishing of `Ext¹` into `𝐆_a` -/

section Vanishing

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- **`Ext¹(g^{-1} j_! j^{-1} ℤ, 𝐆_a) = 0` when `W ×_X Y` is affine.** By Tag 03S6
(`Stacks.EtaleCohomology.extensionByZeroBaseChangeIso`) the inverse image is the extension by zero
along the open `j' : W ×_X Y ⟶ Y` of a constant sheaf; `Ext` out of an extension by zero is `Ext`
out of the sheaf on `W ×_X Y` into the restriction (the adjunction `j'_! ⊣ j'^{-1}` with exact
right adjoint); and the result is `H¹(W ×_X Y, 𝐆_a)`, zero on an affine scheme by Tag 01XB and the
comparison of Tag 03P2. -/
theorem subsingleton_ext_one_inverseImage_extensionByZeroOfRestriction (W : X.Opens)
    [IsAffine (pullback W.ι g)]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [HasExt.{w} (Sheaf (pullback W.ι g).smallEtaleTopology AddCommGrpCat.{u + 1})] :
    Subsingleton (Ext.{w} ((etaleAbelianInverseImage.{u, 0} g).obj
      ((extensionByZeroOfRestriction.{u, 0} W.ι).obj (etaleConstantInt X)))
      (additiveSheaf.{u, u + 1} Y) 1) := by
  let j' := pullback.snd W.ι g
  let f' := pullback.fst W.ι g
  let K := (etaleAbelianInverseImage.{u, 0} f').obj
    ((etaleRestriction.{u, 0} W.ι).obj (etaleConstantInt X))
  have e₁ : (etaleAbelianInverseImage.{u, 0} g).obj
      ((extensionByZeroOfRestriction.{u, 0} W.ι).obj (etaleConstantInt X)) ≅
      (extensionByZero.{u, 0} j').obj K :=
    ((extensionByZeroBaseChangeIso.{u, 0} W.ι g).app _).symm
  have e₂ : K ≅ etaleConstantInt (pullback W.ι g) :=
    (etaleAbelianInverseImage.{u, 0} f').mapIso (etaleRestrictionConstantIso W.ι _) ≪≫
      (etaleAbelianInverseImageConstantIso.{u, 0} f').app _
  have : (etaleRestriction.{u, 0} j').PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (extensionByZeroAdj.{u, 0} j')
  have hP : Subsingleton (Sheaf.H.{w, u + 1} (additiveSheaf.{u, u + 1} (pullback W.ι g)) 1) :=
    subsingleton_sheafH_additiveSheaf_of_isZero_hgroup _ 1 one_pos
      (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen _
        (SheafOfModules.unit (pullback W.ι g).ringCatSheaf) ⊤ (isAffineOpen_top _) 1 one_pos)
  have h₁ : Subsingleton (Ext.{w} K ((etaleRestriction.{u, 0} j').obj
      (additiveSheaf.{u, u + 1} Y)) 1) :=
    (extIsoCongr e₂ (etaleRestrictionAdditiveSheafIso j') 1).injective.subsingleton
  have h₂ := (Stacks.Cohomology.OverObjectCohomology.extAdjEquiv
    (extensionByZeroAdj.{u, 0} j') K (additiveSheaf.{u, u + 1} Y) 1).injective.subsingleton
  exact (extIsoCongr e₁ (Iso.refl _) 1).injective.subsingleton

end Vanishing

/-! ### Morphisms out of `j_! j^{-1} ℤ` -/

section Sections

variable {X : Scheme.{u}} (W : X.Opens)

/-- The final object of the small étale site of an open subscheme `W`. -/
def opensEtaleFinal : (W : Scheme.{u}).Etale :=
  letI : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    (HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
      RingHom.Etale.containsIdentities :
        MorphismProperty.IsMultiplicative
          (@Etale : MorphismProperty Scheme.{u})).toContainsIdentities
  MorphismProperty.Over.mk ⊤ (𝟙 (W : Scheme.{u})) (by infer_instance)

/-- `Stacks.ArtinSchreier.opensEtaleFinal` is a final object. -/
def opensEtaleFinalIsTerminal : IsTerminal (opensEtaleFinal W) :=
  letI : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    (HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
      RingHom.Etale.containsIdentities :
        MorphismProperty.IsMultiplicative
          (@Etale : MorphismProperty Scheme.{u})).toContainsIdentities
  MorphismProperty.Over.mkIdTerminal _ _

/-- The open subscheme `W`, as an object of the small étale site of `X`. -/
abbrev opensEtaleObject : X.Etale :=
  (Scheme.Etale.smallEtaleCompose W.ι).obj (opensEtaleFinal W)

/-- **Morphisms `j_! j^{-1} ℤ_X ⟶ H` are the sections of `H` over `W`**, additively: the
adjunction `j_! ⊣ j^{-1}`, the identification of `j^{-1} ℤ_X` with the constant sheaf, the
constant-sheaf adjunction at the final object of `W_étale`, and `Hom(ℤ, A) = A`. -/
def extensionByZeroOfRestrictionHomAddEquiv (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((extensionByZeroOfRestriction.{u, 0} W.ι).obj (etaleConstantInt X) ⟶ H) ≃+
      H.obj.obj (op (opensEtaleObject W)) :=
  ((extensionByZeroAdj.{u, 0} W.ι).homAddEquiv _ H).trans <|
    ({ toFun := fun φ => (etaleRestrictionConstantIso W.ι _).inv ≫ φ
       invFun := fun ψ => (etaleRestrictionConstantIso W.ι _).hom ≫ ψ
       left_inv := fun φ => by simp
       right_inv := fun ψ => by simp
       map_add' := fun φ ψ => Preadditive.comp_add _ _ _ _ _ _ } :
      ((etaleRestriction.{u, 0} W.ι).obj (etaleConstantInt X) ⟶
          (etaleRestriction.{u, 0} W.ι).obj H) ≃+
        (etaleConstantInt W ⟶ (etaleRestriction.{u, 0} W.ι).obj H)).trans <|
    ((constantSheafAdj _ _ (opensEtaleFinalIsTerminal W)).homAddEquiv _ _).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)

/-- `Stacks.ArtinSchreier.extensionByZeroOfRestrictionHomAddEquiv`, unfolded. -/
theorem extensionByZeroOfRestrictionHomAddEquiv_apply
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (τ : (extensionByZeroOfRestriction.{u, 0} W.ι).obj (etaleConstantInt X) ⟶ H) :
    extensionByZeroOfRestrictionHomAddEquiv W H τ =
      ((constantSheafAdj _ _ (opensEtaleFinalIsTerminal W)).homEquiv _ _
        ((etaleRestrictionConstantIso W.ι _).inv ≫
          (extensionByZeroAdj.{u, 0} W.ι).homEquiv _ _ τ)) (ULift.up 1) :=
  rfl

/-- **Naturality of `Stacks.ArtinSchreier.extensionByZeroOfRestrictionHomAddEquiv` in `H`.** -/
theorem extensionByZeroOfRestrictionHomAddEquiv_comp
    {H H' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (τ : (extensionByZeroOfRestriction.{u, 0} W.ι).obj (etaleConstantInt X) ⟶ H) (m : H ⟶ H') :
    extensionByZeroOfRestrictionHomAddEquiv W H' (τ ≫ m) =
      m.hom.app (op (opensEtaleObject W)) (extensionByZeroOfRestrictionHomAddEquiv W H τ) := by
  rw [extensionByZeroOfRestrictionHomAddEquiv_apply, extensionByZeroOfRestrictionHomAddEquiv_apply,
    (extensionByZeroAdj.{u, 0} W.ι).homEquiv_naturality_right, ← Category.assoc,
    (constantSheafAdj _ _ (opensEtaleFinalIsTerminal W)).homEquiv_naturality_right]
  rfl

end Sections

end Stacks.ArtinSchreier

end
