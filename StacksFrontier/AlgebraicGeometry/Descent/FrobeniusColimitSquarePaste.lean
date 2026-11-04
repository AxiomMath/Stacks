module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitFreeComp

/-!
# Pasting two commutative squares of transition functors over the Frobenius colimits

Let `p` be a prime. For a commutative square of schemes in characteristic `p` the two composite
transition functors of Stacks Tag 0EXE around the square are compared by
`AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso`, and on all sheaves of modules by
`AlgebraicGeometry.frobeniusColimitPullbackSquareIso`. This file proves that **those comparisons
paste**: for two commutative squares glued along an edge,

```
S --g--> T --h--> U
|k        |l       |m
↓         ↓        ↓
S'--g'-> T'--h'-> U'
```

the comparison of the outer square is the composite of the comparisons of the two inner ones,
modulo the composition comparisons of the transition functors along the two horizontal composites.

This is the structural law the trivialising-cover step of [Stacks, Tag 0EXD] needs. Full
faithfulness of the comparison functor of that tag at a general finite locally free module asks
for the Hom-square of the square of Example 0EVH over each member of a trivialising cover of the
base, and the comparison isomorphism over a member has to be matched against the one over the
base. That matching is *not* a comparison of two square isomorphisms over different bases —
stated that way it needs an equality of opens, `q ⁻¹ᵁ (b ⁻¹ᵁ U) = e ⁻¹ᵁ (z ⁻¹ᵁ U)`, which holds
only by transport along the square's commutativity and cannot be rewritten away. Stated as a
pasting law it needs no transport at all: the square comparison is by definition two instances of
`AlgebraicGeometry.frobeniusColimitVectorBundlesPullbackComp` and one `CategoryTheory.eqToIso`,
and the pasting law is the associativity pentagon of those read twice.

## Main definitions

* `AlgebraicGeometry.frobeniusColimitPullbackTriangleIso`: **the comparison of the two extensions
  of scalars attached to a commuting triangle of schemes**, with the composite kept as a variable
  subject to an equation rather than written out.

## Main results

* `AlgebraicGeometry.frobeniusColimitPullbackTriangleIso_pentagon_app`: **the associativity
  pentagon of those comparisons**, with all four composites as variables.
* `AlgebraicGeometry.frobeniusColimitPullbackSquareIso_paste_app` and
  `AlgebraicGeometry.frobeniusColimitPullbackSquareIso_paste`: **the pasting law on all sheaves of
  modules**, on an object and as an equality of natural isomorphisms.
* `AlgebraicGeometry.frobeniusColimitVectorBundlesSquareIso_paste`: **the pasting law on the
  finite locally free modules**, which is the form the comparison functor of Stacks Tag 0EXD is
  built from.
* `AlgebraicGeometry.frobeniusColimitPullbackSquareIso_cube_app`: **the cube coherence** — for two
  commutative squares joined by four vertical morphisms making the four side faces commute, the
  two routes around the cube agree. This is the pasting law read twice at one and the same
  rectangle.

## Implementation notes

Keeping the composite `fg` of a commuting triangle a variable subject to `f ≫ g = fg`, rather than
writing `f ≫ g`, is what makes the pentagon usable: a consumer instantiates it at whichever
morphism its diagram actually names and supplies the equation, instead of having to produce a
diagram in which every composite is literal. The same device is already used for the *ring-sheaf*
morphisms by `AlgebraicGeometry.frobeniusColimitPullbackCompOfEq`, whose associativity pentagon
`AlgebraicGeometry.frobeniusColimitPullbackCompOfEq_assoc` is what discharges the pentagon here;
the two devices are complementary, one varying the morphism of schemes and the other the induced
morphism of Frobenius-colimit sheaves of rings.

Composition of morphisms of schemes is *definitionally* associative, so
`(f ≫ g) ≫ h` and `f ≫ g ≫ h` induce the same morphism of Frobenius-colimit sheaves of rings on
the nose; that is why the pentagon's four transports all reduce to the identity once the three
triangles' equations are substituted.

The transport of the pasting law from all sheaves of modules to the finite locally free ones is
the idiom of `AlgebraicGeometry.frobeniusVectPullbackIso_comp`: an equality of natural
isomorphisms of functors into a full subcategory is tested on components, and a morphism of the
subcategory is determined by the morphism of sheaves of modules underlying it.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

/-! ### Restriction along a commuting triangle of schemes -/

section Triangle

variable {Q R S T : Scheme.{u}}

/-- **The comparison of the two extensions of scalars attached to a commuting triangle of
schemes**, on all sheaves of modules over the Frobenius colimits of the structure sheaves. Given
`f ≫ g = fg`, extending scalars along the transition of `g` and then along that of `f` agrees with
extending them along the transition of `fg`.

Keeping `fg` a variable subject to an equation, rather than writing the composite `f ≫ g`, is what
makes the associativity constraint usable: see
`AlgebraicGeometry.frobeniusColimitPullbackTriangleIso_pentagon_app`. -/
noncomputable def frobeniusColimitPullbackTriangleIso (f : R ⟶ S) (g : S ⟶ T) (fg : R ⟶ T)
    (hR : IsInCharacteristic R p) (hS : IsInCharacteristic S p) (hT : IsInCharacteristic T p)
    (w : f ≫ g = fg) :
    _root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p g hS hT) ⋙
        _root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p f hR hS) ≅
      _root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p fg hR hT) :=
  frobeniusColimitPullbackComp p f g hR hS hT ≪≫
    eqToIso (congrArg (fun m : R ⟶ T => _root_.SheafOfModules.pullback.{u}
      (frobeniusColimitStructureSheafHom p m hR hT)) w)

/-- At the literal composite, the comparison of
`AlgebraicGeometry.frobeniusColimitPullbackTriangleIso` is
`AlgebraicGeometry.frobeniusColimitPullbackComp`. -/
@[simp]
lemma frobeniusColimitPullbackTriangleIso_rfl (f : R ⟶ S) (g : S ⟶ T)
    (hR : IsInCharacteristic R p) (hS : IsInCharacteristic S p) (hT : IsInCharacteristic T p) :
    frobeniusColimitPullbackTriangleIso p f g (f ≫ g) hR hS hT rfl =
      frobeniusColimitPullbackComp p f g hR hS hT := by
  simp only [frobeniusColimitPullbackTriangleIso]
  exact Iso.trans_refl _

/-- **The associativity pentagon of the comparisons of extension of scalars along the transition
functors, written for commuting triangles.** For `f`, `g`, `h` composable morphisms of schemes in
characteristic `p` and any morphisms `fg`, `gh`, `fgh` filling the four triangles they span, the
two ways of comparing extension of scalars along the transitions of `h`, `g`, `f` in turn with
extension of scalars along the transition of `fgh` agree.

This is `AlgebraicGeometry.frobeniusColimitPullbackCompOfEq_assoc` with the *scheme* composites
replaced by variables; that lemma already has the induced morphisms of Frobenius-colimit sheaves
of rings as variables, and both devices are needed because a diagram names its morphisms of
schemes and its morphisms of sheaves of rings independently. -/
@[reassoc]
theorem frobeniusColimitPullbackTriangleIso_pentagon_app (f : Q ⟶ R) (g : R ⟶ S) (h : S ⟶ T)
    (fg : Q ⟶ S) (gh : R ⟶ T) (fgh : Q ⟶ T)
    (hQ : IsInCharacteristic Q p) (hR : IsInCharacteristic R p) (hS : IsInCharacteristic S p)
    (hT : IsInCharacteristic T p)
    (wfg : f ≫ g = fg) (wgh : g ≫ h = gh) (w₁ : f ≫ gh = fgh) (w₂ : fg ≫ h = fgh)
    (M : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf T p hT)) :
    (frobeniusColimitPullbackTriangleIso p f g fg hQ hR hS wfg).hom.app
          ((_root_.SheafOfModules.pullback.{u}
            (frobeniusColimitStructureSheafHom p h hS hT)).obj M) ≫
        (frobeniusColimitPullbackTriangleIso p fg h fgh hQ hS hT w₂).hom.app M =
      (_root_.SheafOfModules.pullback.{u}
            (frobeniusColimitStructureSheafHom p f hQ hR)).map
          ((frobeniusColimitPullbackTriangleIso p g h gh hR hS hT wgh).hom.app M) ≫
        (frobeniusColimitPullbackTriangleIso p f gh fgh hQ hR hT w₁).hom.app M := by
  subst wfg wgh w₁
  have H := NatTrans.congr_app (congrArg Iso.hom
    (frobeniusColimitPullbackCompOfEq_assoc p f g h hQ hR hS hT
      (frobeniusColimitStructureSheafHom p h hS hT)
      (frobeniusColimitStructureSheafHom p g hR hS)
      (frobeniusColimitStructureSheafHom p f hQ hR)
      (frobeniusColimitStructureSheafHom p (g ≫ h) hR hT)
      (frobeniusColimitStructureSheafHom_comp p g h hR hS hT)
      (frobeniusColimitStructureSheafHom p (f ≫ g) hQ hS)
      (frobeniusColimitStructureSheafHom_comp p f g hQ hR hS)
      (frobeniusColimitStructureSheafHom p (f ≫ g ≫ h) hQ hT)
      (frobeniusColimitStructureSheafHom_comp p (f ≫ g) h hQ hS hT)
      (frobeniusColimitStructureSheafHom_comp p f (g ≫ h) hQ hR hT))) M
  -- The composite `(f ≫ g) ≫ h` is `f ≫ g ≫ h` definitionally, so the triangle filled by `w₂`
  -- is the literal one and its transport is the identity.
  have h₂ : frobeniusColimitPullbackTriangleIso p (f ≫ g) h (f ≫ g ≫ h) hQ hS hT w₂ =
      frobeniusColimitPullbackComp p (f ≫ g) h hQ hS hT :=
    frobeniusColimitPullbackTriangleIso_rfl p (f ≫ g) h hQ hS hT
  rw [h₂, frobeniusColimitPullbackTriangleIso_rfl,
    frobeniusColimitPullbackTriangleIso_rfl, frobeniusColimitPullbackTriangleIso_rfl]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] at H
  exact H

end Triangle

/-! ### Pasting two commutative squares -/

section Paste

/-- The comparison of `AlgebraicGeometry.frobeniusColimitPullbackSquareIso` written through the
comparison for the commuting triangle on its first two edges. -/
lemma frobeniusColimitPullbackSquareIso_hom_app {X X' Z E : Scheme.{u}} (b : X' ⟶ X)
    (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z) (hX : IsInCharacteristic X p)
    (hX' : IsInCharacteristic X' p) (hZ : IsInCharacteristic Z p)
    (hE : IsInCharacteristic E p) (hw : q ≫ b = e ≫ z)
    (M : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)) :
    (frobeniusColimitPullbackSquareIso p b z q e hX hX' hZ hE hw).hom.app M =
      (frobeniusColimitPullbackTriangleIso p e z (q ≫ b) hE hZ hX hw.symm).hom.app M ≫
        (frobeniusColimitPullbackComp p q b hE hX' hX).inv.app M := by
  simp only [frobeniusColimitPullbackSquareIso, frobeniusColimitPullbackTriangleIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]

variable {X Y Z X' Y' Z' : Scheme.{u}}

/-- **The comparison attached to a horizontal pasting of two commutative squares of schemes is the
pasting of the two comparisons, on all sheaves of modules over the Frobenius colimits**, stated on
an object. Given the two commutative squares `g ≫ l = k ≫ g'` and `h ≫ m = l ≫ h'`, the outer
square `(g ≫ h) ≫ m = k ≫ g' ≫ h'` commutes, and its comparison is obtained by composing the two
inner comparisons with the comparisons for the two horizontal composites.

The two horizontal composites `gh` and `g'h'` are variables subject to equations, so that one and
the same outer square serves two different pastings of one rectangle: that is what makes the cube
coherence of `AlgebraicGeometry.frobeniusColimitPullbackSquareIso_cube_app` a transitivity of two
instances of this law and nothing more. -/
theorem frobeniusColimitPullbackSquareIso_paste_app (g : X ⟶ Y) (h : Y ⟶ Z) (k : X ⟶ X')
    (l : Y ⟶ Y') (m : Z ⟶ Z') (g' : X' ⟶ Y') (h' : Y' ⟶ Z')
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (hZ : IsInCharacteristic Z p)
    (hX' : IsInCharacteristic X' p) (hY' : IsInCharacteristic Y' p)
    (hZ' : IsInCharacteristic Z' p)
    (w₁ : g ≫ l = k ≫ g') (w₂ : h ≫ m = l ≫ h')
    (gh : X ⟶ Z) (wgh : g ≫ h = gh) (g'h' : X' ⟶ Z') (wg'h' : g' ≫ h' = g'h')
    (w : gh ≫ m = k ≫ g'h')
    (M : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf Z' p hZ')) :
    (frobeniusColimitPullbackTriangleIso p g h gh hX hY hZ wgh).hom.app
          ((_root_.SheafOfModules.pullback.{u}
            (frobeniusColimitStructureSheafHom p m hZ hZ')).obj M) ≫
        (frobeniusColimitPullbackSquareIso p g'h' m k gh
          hZ' hX' hZ hX w.symm).hom.app M =
      (_root_.SheafOfModules.pullback.{u}
            (frobeniusColimitStructureSheafHom p g hX hY)).map
          ((frobeniusColimitPullbackSquareIso p h' m l h hZ' hY' hZ hY w₂.symm).hom.app M) ≫
        (frobeniusColimitPullbackSquareIso p g' l k g hY' hX' hY hX w₁.symm).hom.app
            ((_root_.SheafOfModules.pullback.{u}
              (frobeniusColimitStructureSheafHom p h' hY' hZ')).obj M) ≫
          (_root_.SheafOfModules.pullback.{u}
              (frobeniusColimitStructureSheafHom p k hX hX')).map
            ((frobeniusColimitPullbackTriangleIso p g' h' g'h' hX' hY' hZ'
              wg'h').hom.app M) := by
  subst wgh wg'h'
  simp only [frobeniusColimitPullbackTriangleIso_rfl]
  have hd : (k ≫ g') ≫ h' = k ≫ g' ≫ h' := Category.assoc k g' h'
  have hwa : g ≫ l ≫ h' = k ≫ g' ≫ h' := by rw [← Category.assoc, w₁, Category.assoc]
  have TA1 := frobeniusColimitPullbackTriangleIso_pentagon_app p g h m (g ≫ h) (l ≫ h')
    (k ≫ g' ≫ h') hX hY hZ hZ' rfl w₂ hwa w M
  have TA2 := frobeniusColimitPullbackTriangleIso_pentagon_app p k g' h' (k ≫ g') (g' ≫ h')
    (k ≫ g' ≫ h') hX hX' hY' hZ' rfl rfl rfl hd M
  have TA3 := frobeniusColimitPullbackTriangleIso_pentagon_app p g l h' (k ≫ g') (l ≫ h')
    (k ≫ g' ≫ h') hX hY hY' hZ' w₁ rfl hwa hd M
  have hmap : (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p g hX hY)).map
        ((frobeniusColimitPullbackComp p l h' hY hY' hZ').inv.app M) ≫
      (_root_.SheafOfModules.pullback.{u}
        (frobeniusColimitStructureSheafHom p g hX hY)).map
        ((frobeniusColimitPullbackComp p l h' hY hY' hZ').hom.app M) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  simp only [frobeniusColimitPullbackTriangleIso_rfl] at TA1 TA2 TA3
  apply (cancel_mono ((frobeniusColimitPullbackComp p k (g' ≫ h') hX hX' hZ').hom.app M)).mp
  simp only [frobeniusColimitPullbackSquareIso_hom_app, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]
  rw [TA1, ← TA2]
  simp only [Iso.inv_hom_id_app_assoc, TA3, reassoc_of% hmap]

/-- **The comparison attached to a horizontal pasting of two commutative squares of schemes is the
pasting of the two comparisons, on all sheaves of modules over the Frobenius colimits.** This is
`AlgebraicGeometry.frobeniusColimitPullbackSquareIso_paste_app` read as an equality of natural
isomorphisms. -/
theorem frobeniusColimitPullbackSquareIso_paste (g : X ⟶ Y) (h : Y ⟶ Z) (k : X ⟶ X')
    (l : Y ⟶ Y') (m : Z ⟶ Z') (g' : X' ⟶ Y') (h' : Y' ⟶ Z')
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (hZ : IsInCharacteristic Z p)
    (hX' : IsInCharacteristic X' p) (hY' : IsInCharacteristic Y' p)
    (hZ' : IsInCharacteristic Z' p)
    (w₁ : g ≫ l = k ≫ g') (w₂ : h ≫ m = l ≫ h') (w : (g ≫ h) ≫ m = k ≫ g' ≫ h') :
    Functor.isoWhiskerLeft (_root_.SheafOfModules.pullback.{u}
            (frobeniusColimitStructureSheafHom p m hZ hZ'))
          (frobeniusColimitPullbackComp p g h hX hY hZ) ≪≫
        frobeniusColimitPullbackSquareIso p (g' ≫ h') m k (g ≫ h) hZ' hX' hZ hX w.symm =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
            (frobeniusColimitPullbackSquareIso p h' m l h hZ' hY' hZ hY w₂.symm)
            (_root_.SheafOfModules.pullback.{u}
              (frobeniusColimitStructureSheafHom p g hX hY)) ≪≫
          Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft (_root_.SheafOfModules.pullback.{u}
                  (frobeniusColimitStructureSheafHom p h' hY' hZ'))
                (frobeniusColimitPullbackSquareIso p g' l k g hY' hX' hY hX w₁.symm) ≪≫
              (Functor.associator _ _ _).symm ≪≫
                Functor.isoWhiskerRight
                  (frobeniusColimitPullbackComp p g' h' hX' hY' hZ')
                  (_root_.SheafOfModules.pullback.{u}
                    (frobeniusColimitStructureSheafHom p k hX hX')) :=
  Iso.ext (NatTrans.ext (funext fun M ↦ by
    have H := frobeniusColimitPullbackSquareIso_paste_app p g h k l m g' h'
      hX hY hZ hX' hY' hZ' w₁ w₂ (g ≫ h) rfl (g' ≫ h') rfl w M
    simp only [frobeniusColimitPullbackTriangleIso_rfl] at H
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
    exact H))

/-! ### The cube coherence -/

section Cube

variable {R S₁ S₂ T : Scheme.{u}}

/-- **Two factorisations of one morphism differ by the square comparison of the square they
span.** For `f₁ ≫ g₁ = f₂ ≫ g₂ = fg`, the comparison for the triangle filled by the second
factorisation is the square comparison of that square followed by the comparison for the triangle
filled by the first.

Both factorisations of `fg` occur in the cube coherence below, one from each of the two pastings,
and this is what identifies them. -/
lemma frobeniusColimitPullbackSquareIso_hom_app_comp_triangleIso (f₁ : R ⟶ S₁) (g₁ : S₁ ⟶ T)
    (f₂ : R ⟶ S₂) (g₂ : S₂ ⟶ T) (hR : IsInCharacteristic R p)
    (hS₁ : IsInCharacteristic S₁ p) (hS₂ : IsInCharacteristic S₂ p)
    (hT : IsInCharacteristic T p) (sq : f₁ ≫ g₁ = f₂ ≫ g₂) (fg : R ⟶ T)
    (hfg : f₁ ≫ g₁ = fg)
    (N : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf T p hT)) :
    (frobeniusColimitPullbackSquareIso p g₁ g₂ f₁ f₂ hT hS₁ hS₂ hR sq).hom.app N ≫
        (frobeniusColimitPullbackTriangleIso p f₁ g₁ fg hR hS₁ hT hfg).hom.app N =
      (frobeniusColimitPullbackTriangleIso p f₂ g₂ fg hR hS₂ hT
        (sq.symm.trans hfg)).hom.app N := by
  subst hfg
  rw [frobeniusColimitPullbackSquareIso_hom_app, frobeniusColimitPullbackTriangleIso_rfl,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

end Cube

section CubeFaces

variable {X X' Z E V V' W D : Scheme.{u}}

/-- **The cube coherence of the square comparisons.** Given two commutative squares of schemes in
characteristic `p` — a "bottom" one `q ≫ b = e ≫ z` with corners `X`, `X'`, `Z`, `E`, and a "top"
one `qV ≫ bV = eV ≫ zV` with corners `V`, `V'`, `W`, `D` — together with four vertical morphisms
`ιV`, `ιV'`, `ιW`, `ιD` making the four side faces commute, the two routes around the resulting
cube agree: the `q`-side face followed by the `b`-side face and the top face equals the bottom face
followed by the `e`-side face and the `z`-side face.

Each route is the pasting of one and the same rectangle `D ⟶ X` along the diagonal `qV ≫ ιV'`, by
`AlgebraicGeometry.frobeniusColimitPullbackSquareIso_paste_app`; the coherence is their
transitivity, with the two factorisations of each diagonal identified by
`AlgebraicGeometry.frobeniusColimitPullbackSquareIso_hom_app_comp_triangleIso`. All six faces
appear exactly once, and no comparison for a composite survives.

**This is the form the trivialising-cover step of [Stacks, Tag 0EXD] needs**, and the reason every
scheme, morphism and commutativity is a parameter is that at the square of Example 0EVH over a
basic open `D(g)` of the base the fourth corner `D` of the top face is `e ⁻¹ᵁ (z ⁻¹ᵁ D(g))` read
one way and `q ⁻¹ᵁ (b ⁻¹ᵁ D(g))` read the other. Those two opens are equal only by transport along
the bottom square's own commutativity, so a statement that *computed* the top face from the bottom
one and the open would carry that transport inside its type, where no rewrite reaches it. Here the
consumer picks one of the two and supplies the four side commutativities as ordinary equations
between morphisms of schemes. -/
theorem frobeniusColimitPullbackSquareIso_cube_app
    (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
    (bV : V' ⟶ V) (zV : W ⟶ V) (qV : D ⟶ V') (eV : D ⟶ W)
    (ιV : V ⟶ X) (ιV' : V' ⟶ X') (ιW : W ⟶ Z) (ιD : D ⟶ E)
    (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
    (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p)
    (hV : IsInCharacteristic V p) (hV' : IsInCharacteristic V' p)
    (hW : IsInCharacteristic W p) (hD : IsInCharacteristic D p)
    (hw : q ≫ b = e ≫ z) (hwV : qV ≫ bV = eV ≫ zV)
    (sb : bV ≫ ιV = ιV' ≫ b) (sz : zV ≫ ιV = ιW ≫ z)
    (sq : qV ≫ ιV' = ιD ≫ q) (se : eV ≫ ιW = ιD ≫ e)
    (M : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf X p hX)) :
    (frobeniusColimitPullbackSquareIso p ιV' q qV ιD hX' hV' hE hD sq).hom.app
          ((_root_.SheafOfModules.pullback.{u}
            (frobeniusColimitStructureSheafHom p b hX' hX)).obj M) ≫
        (_root_.SheafOfModules.pullback.{u}
              (frobeniusColimitStructureSheafHom p qV hD hV')).map
            ((frobeniusColimitPullbackSquareIso p ιV b bV ιV'
              hX hV hX' hV' sb).hom.app M) ≫
          (frobeniusColimitPullbackSquareIso p zV bV eV qV
              hV hW hV' hD hwV.symm).hom.app
            ((_root_.SheafOfModules.pullback.{u}
              (frobeniusColimitStructureSheafHom p ιV hV hX)).obj M) =
      (_root_.SheafOfModules.pullback.{u}
            (frobeniusColimitStructureSheafHom p ιD hD hE)).map
          ((frobeniusColimitPullbackSquareIso p z b e q hX hZ hX' hE hw.symm).hom.app M) ≫
        (frobeniusColimitPullbackSquareIso p ιW e eV ιD hZ hW hE hD se).hom.app
            ((_root_.SheafOfModules.pullback.{u}
              (frobeniusColimitStructureSheafHom p z hZ hX)).obj M) ≫
          (_root_.SheafOfModules.pullback.{u}
              (frobeniusColimitStructureSheafHom p eV hD hW)).map
            ((frobeniusColimitPullbackSquareIso p ιV z zV ιW
              hX hV hZ hW sz).hom.app M) := by
  have hcube : (qV ≫ ιV') ≫ b = eV ≫ zV ≫ ιV := by
    rw [Category.assoc, ← sb, ← Category.assoc, hwV, Category.assoc]
  have h1 := frobeniusColimitPullbackSquareIso_paste_app p qV ιV' eV bV b zV ιV
    hD hV' hX' hW hV hX hwV sb.symm (qV ≫ ιV') rfl (zV ≫ ιV) rfl hcube M
  have h2 := frobeniusColimitPullbackSquareIso_paste_app p ιD q eV e b ιW z
    hD hE hX' hW hZ hX se.symm hw (qV ≫ ιV') (sq.symm.trans rfl)
    (zV ≫ ιV) (sz.symm.trans rfl) hcube M
  have h3 := frobeniusColimitPullbackSquareIso_hom_app_comp_triangleIso p qV ιV' ιD q
    hD hV' hE hX' sq (qV ≫ ιV') rfl
    ((_root_.SheafOfModules.pullback.{u}
      (frobeniusColimitStructureSheafHom p b hX' hX)).obj M)
  have h4 := frobeniusColimitPullbackSquareIso_hom_app_comp_triangleIso p zV ιV ιW z
    hW hV hZ hX sz (zV ≫ ιV) rfl M
  simp only [frobeniusColimitPullbackTriangleIso_rfl] at h1 h2 h3 h4
  apply (cancel_mono ((_root_.SheafOfModules.pullback.{u}
    (frobeniusColimitStructureSheafHom p eV hD hW)).map
      ((frobeniusColimitPullbackComp p zV ιV hW hV hX).hom.app M))).mp
  simp only [Category.assoc]
  rw [← Functor.map_comp, h4, ← h2, ← h3, Category.assoc, h1]

end CubeFaces

/-! ### The pasting law on the finite locally free modules -/

/-- The underlying sheaf of modules of a transition of a finite locally free module. -/
@[simp]
lemma frobeniusColimitVectorBundlesPullback_obj_obj {V W : Scheme.{u}} (f : V ⟶ W)
    (hV : IsInCharacteristic V p) (hW : IsInCharacteristic W p)
    (M : frobeniusColimitVectorBundles W p hW) :
    ((frobeniusColimitVectorBundlesPullback p f hV hW).obj M).obj =
      (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p f hV hW)).obj
        M.obj :=
  rfl

/-- The underlying morphism of sheaves of modules of a transition of a morphism of finite locally
free modules. -/
@[simp]
lemma frobeniusColimitVectorBundlesPullback_map_hom {V W : Scheme.{u}} (f : V ⟶ W)
    (hV : IsInCharacteristic V p) (hW : IsInCharacteristic W p)
    {M N : frobeniusColimitVectorBundles W p hW} (φ : M ⟶ N) :
    ((frobeniusColimitVectorBundlesPullback p f hV hW).map φ).hom =
      (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p f hV hW)).map
        φ.hom :=
  rfl

/-- **The comparison attached to a horizontal pasting of two commutative squares of schemes is the
pasting of the two comparisons, on the finite locally free modules over the Frobenius colimits.**

This is `AlgebraicGeometry.frobeniusColimitPullbackSquareIso_paste` transported to the full
subcategories of finite locally free modules, which are the fibre categories of the category
fibred in groupoids of Stacks Tag 0EXE and the categories the comparison functor of Stacks Tag
0EXD is a functor between. -/
theorem frobeniusColimitVectorBundlesSquareIso_paste (g : X ⟶ Y) (h : Y ⟶ Z) (k : X ⟶ X')
    (l : Y ⟶ Y') (m : Z ⟶ Z') (g' : X' ⟶ Y') (h' : Y' ⟶ Z')
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) (hZ : IsInCharacteristic Z p)
    (hX' : IsInCharacteristic X' p) (hY' : IsInCharacteristic Y' p)
    (hZ' : IsInCharacteristic Z' p)
    (w₁ : g ≫ l = k ≫ g') (w₂ : h ≫ m = l ≫ h') (w : (g ≫ h) ≫ m = k ≫ g' ≫ h') :
    Functor.isoWhiskerLeft (frobeniusColimitVectorBundlesPullback p m hZ hZ')
          (frobeniusColimitVectorBundlesPullbackComp p g h hX hY hZ) ≪≫
        frobeniusColimitVectorBundlesSquareIso p (g' ≫ h') m k (g ≫ h)
          hZ' hX' hZ hX w.symm =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
            (frobeniusColimitVectorBundlesSquareIso p h' m l h hZ' hY' hZ hY w₂.symm)
            (frobeniusColimitVectorBundlesPullback p g hX hY) ≪≫
          Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft (frobeniusColimitVectorBundlesPullback p h' hY' hZ')
                (frobeniusColimitVectorBundlesSquareIso p g' l k g hY' hX' hY hX w₁.symm) ≪≫
              (Functor.associator _ _ _).symm ≪≫
                Functor.isoWhiskerRight
                  (frobeniusColimitVectorBundlesPullbackComp p g' h' hX' hY' hZ')
                  (frobeniusColimitVectorBundlesPullback p k hX hX') :=
  Iso.ext (NatTrans.ext (funext fun M ↦ ObjectProperty.hom_ext _ (by
    have H := frobeniusColimitPullbackSquareIso_paste_app p g h k l m g' h'
      hX hY hZ hX' hY' hZ' w₁ w₂ (g ≫ h) rfl (g' ≫ h') rfl w M.obj
    simpa [frobeniusColimitVectorBundlesPullbackComp_hom_app_hom,
      frobeniusColimitVectorBundlesSquareIso_hom_app_hom] using H)))

end Paste

end AlgebraicGeometry

end
