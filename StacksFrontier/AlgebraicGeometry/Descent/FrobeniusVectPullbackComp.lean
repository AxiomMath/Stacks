module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusVectPower

/-!
# The Frobenius comparison is compatible with composition of restrictions

Let `p` be a prime and let `g : X ⟶ Y` and `h : Y ⟶ Z` be morphisms of schemes in
characteristic `p`. Restriction of vector bundles commutes with Frobenius pullback
(`AlgebraicGeometry.frobeniusVectPullbackIso`), and restriction along a composite is the
composite of the restrictions (`AlgebraicGeometry.Scheme.Vect.pullbackComp`). This file proves
that the two structures are compatible: the comparison for `g ≫ h` is the horizontal pasting
of the comparisons for `h` and for `g`.

## Main results

* `AlgebraicGeometry.modulesPullbackTriangleIso_pentagon_app`: the associativity constraint of
  the pullback pseudofunctor, written for the comparison attached to a commuting triangle.
* `AlgebraicGeometry.modulesPullbackSquareIso_paste`: the comparison attached to the
  horizontal pasting of two commuting squares of schemes is the pasting of the two
  comparisons, on all sheaves of modules.
* `AlgebraicGeometry.frobeniusModulesPullbackIso_comp` and
  `AlgebraicGeometry.frobeniusVectPullbackIso_comp`: the instance of that compatibility for the
  two Frobenius naturality squares of `g` and `h`, on all sheaves of modules and on vector
  bundles.

## Implementation notes

The comparison `AlgebraicGeometry.modulesPullbackSquareIso` of the two double restrictions
attached to a commuting square is built from `AlgebraicGeometry.Scheme.Modules.pullbackComp`
and `AlgebraicGeometry.Scheme.Modules.pullbackCongr`, so the compatibility proved here is a
three-dimensional coherence: it is the associativity constraint
`AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity` used three times. To apply that
constraint one needs it in a form where the composites it mentions are *variables* subject to
equations rather than literal composites, which is what
`AlgebraicGeometry.modulesPullbackTriangleIso` and
`AlgebraicGeometry.modulesPullbackTriangleIso_pentagon_app` provide: once the variables are
substituted away, the equations become `rfl` and the constraint applies on the nose.

Everything is proved for a general commuting square, with the four morphisms still variables,
and only then specialised to the Frobenius naturality squares; unfolding the structural
isomorphisms at the concrete morphisms `absoluteFrobenius …` is avoided throughout. Descending
from sheaves of modules to vector bundles uses only the component lemmas
`AlgebraicGeometry.frobeniusVectPullbackIso_hom_app_hom` and
`AlgebraicGeometry.Scheme.Vect.pullbackComp_hom_app_hom` together with
`CategoryTheory.ObjectProperty.hom_ext`.

## References

* [Stacks Project, Tag 0EXC](https://stacks.math.columbia.edu/tag/0EXC)
-/

@[expose] public section

open CategoryTheory Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-! ### Restriction along a commuting triangle of schemes -/

section Triangle

variable {W X Y Z : Scheme.{u}}

/-- Applying a functor to the inverse and then the forward component of a natural isomorphism
gives the identity. -/
private theorem map_inv_app_comp_map_hom_app {C D E : Type*} [Category C] [Category D]
    [Category E] (F : D ⥤ E) {G H : C ⥤ D} (e : G ≅ H) (X : C) :
    F.map (e.inv.app X) ≫ F.map (e.hom.app X) = 𝟙 _ := by
  rw [← Functor.map_comp, Iso.inv_hom_id_app]
  exact F.map_id _

/-- **The canonical comparison of the two restrictions attached to a commuting triangle of
schemes, on all sheaves of modules.** Given `f ≫ g = fg`, restricting along `g` and then along
`f` agrees with restricting along `fg`. Keeping `fg` a variable subject to an equation, rather
than writing the composite `f ≫ g`, is what makes the associativity constraint of pullback
usable: see `AlgebraicGeometry.modulesPullbackTriangleIso_pentagon_app`. -/
noncomputable def modulesPullbackTriangleIso (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (w : f ≫ g = fg) :
    Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f ≅ Scheme.Modules.pullback fg :=
  Scheme.Modules.pullbackComp f g ≪≫ Scheme.Modules.pullbackCongr w

/-- For the literal composite the comparison of
`AlgebraicGeometry.modulesPullbackTriangleIso` is
`AlgebraicGeometry.Scheme.Modules.pullbackComp`. -/
@[simp]
lemma modulesPullbackTriangleIso_rfl (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulesPullbackTriangleIso f g (f ≫ g) rfl = Scheme.Modules.pullbackComp f g := by
  simp [modulesPullbackTriangleIso, Scheme.Modules.pullbackCongr]

/-- **The associativity constraint of pullback of sheaves of modules, written for commuting
triangles.** For `f`, `g`, `h` composable and any morphisms `fg`, `gh`, `fgh` filling the four
triangles, the two ways of comparing `h^* ⋙ g^* ⋙ f^*` with `fgh^*` agree. This is
`AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity` with the composites replaced by
variables. -/
@[reassoc]
theorem modulesPullbackTriangleIso_pentagon_app (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z) (wfg : f ≫ g = fg) (wgh : g ≫ h = gh)
    (w₁ : f ≫ gh = fgh) (w₂ : fg ≫ h = fgh) (M : Z.Modules) :
    (modulesPullbackTriangleIso f g fg wfg).hom.app
          ((Scheme.Modules.pullback h).obj M) ≫
        (modulesPullbackTriangleIso fg h fgh w₂).hom.app M =
      (Scheme.Modules.pullback f).map
          ((modulesPullbackTriangleIso g h gh wgh).hom.app M) ≫
        (modulesPullbackTriangleIso f gh fgh w₁).hom.app M := by
  subst wfg wgh w₁
  have H := NatTrans.congr_app
    (Scheme.Modules.pseudofunctor_associativity (f := f) (g := g) (h := h)) M
  have hmap := map_inv_app_comp_map_hom_app (Scheme.Modules.pullback f)
    (Scheme.Modules.pullbackComp g h) M
  have hepi : Epi ((Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M)) :=
    epi_comp' (IsIso.epi_of_iso ((Scheme.Modules.pullbackComp f (g ≫ h)).app M).inv)
      (IsIso.epi_of_iso ((Scheme.Modules.pullback f).mapIso
        ((Scheme.Modules.pullbackComp g h).app M)).inv)
  apply (cancel_epi ((Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M ≫
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M))).1
  simp only [modulesPullbackTriangleIso, Scheme.Modules.pullbackCongr, eqToIso.hom,
    Iso.trans_hom, NatTrans.comp_app, Category.assoc, eqToHom_app, eqToHom_refl,
    Category.comp_id, reassoc_of% hmap, Iso.inv_hom_id_app, Category.id_comp,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app] at H ⊢
  rw [reassoc_of% H]
  simp

end Triangle

/-! ### Pasting two commuting squares of schemes -/

section Paste

variable {W X Y Z : Scheme.{u}}

/-- The comparison of `AlgebraicGeometry.modulesPullbackSquareIso` written through the
comparison for the commuting triangle on its first two edges. -/
lemma modulesPullbackSquareIso_hom_app {a : W ⟶ Y} {b : Y ⟶ X} {c : W ⟶ Z} {d : Z ⟶ X}
    (w : a ≫ b = c ≫ d) (M : X.Modules) :
    (modulesPullbackSquareIso w).hom.app M =
      (modulesPullbackTriangleIso a b (c ≫ d) w).hom.app M ≫
        (Scheme.Modules.pullbackComp c d).inv.app M := by
  simp [modulesPullbackSquareIso, modulesPullbackTriangleIso]

variable {X' Y' Z' : Scheme.{u}}

/-- **The comparison attached to a horizontal pasting of two commuting squares of schemes is
the pasting of the two comparisons, on all sheaves of modules**, stated on an object. Given the
two commuting squares `g ≫ l = k ≫ g'` and `h ≫ m = l ≫ h'`, the outer square
`(g ≫ h) ≫ m = k ≫ (g' ≫ h')` commutes, and its comparison is obtained by composing the two
inner comparisons. -/
theorem modulesPullbackSquareIso_paste_app (g : X ⟶ Y) (h : Y ⟶ Z) (k : X ⟶ X') (l : Y ⟶ Y')
    (m : Z ⟶ Z') (g' : X' ⟶ Y') (h' : Y' ⟶ Z') (w₁ : g ≫ l = k ≫ g')
    (w₂ : h ≫ m = l ≫ h') (w : (g ≫ h) ≫ m = k ≫ g' ≫ h') (M : Z'.Modules) :
    (Scheme.Modules.pullbackComp g h).hom.app ((Scheme.Modules.pullback m).obj M) ≫
        (modulesPullbackSquareIso w).hom.app M =
      (Scheme.Modules.pullback g).map ((modulesPullbackSquareIso w₂).hom.app M) ≫
        (modulesPullbackSquareIso w₁).hom.app ((Scheme.Modules.pullback h').obj M) ≫
          (Scheme.Modules.pullback k).map
            ((Scheme.Modules.pullbackComp g' h').hom.app M) := by
  have hd : (k ≫ g') ≫ h' = k ≫ g' ≫ h' := Category.assoc k g' h'
  have hw : g ≫ l ≫ h' = k ≫ g' ≫ h' := by rw [← Category.assoc, w₁, Category.assoc]
  have TA1 := modulesPullbackTriangleIso_pentagon_app g h m (g ≫ h) (l ≫ h')
    (k ≫ g' ≫ h') rfl w₂ hw w M
  have TA2 := modulesPullbackTriangleIso_pentagon_app k g' h' (k ≫ g') (g' ≫ h')
    (k ≫ g' ≫ h') rfl rfl rfl hd M
  have TA3 := modulesPullbackTriangleIso_pentagon_app g l h' (k ≫ g') (l ≫ h')
    (k ≫ g' ≫ h') w₁ rfl hw hd M
  have hmap := map_inv_app_comp_map_hom_app (Scheme.Modules.pullback g)
    (Scheme.Modules.pullbackComp l h') M
  simp only [modulesPullbackTriangleIso_rfl] at TA1 TA2 TA3
  apply (cancel_mono ((Scheme.Modules.pullbackComp k (g' ≫ h')).hom.app M)).mp
  simp only [modulesPullbackSquareIso_hom_app, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]
  rw [TA1, ← TA2]
  simp only [Iso.inv_hom_id_app_assoc, TA3, reassoc_of% hmap]

/-- **The comparison attached to a horizontal pasting of two commuting squares of schemes is
the pasting of the two comparisons, on all sheaves of modules.** This is
`AlgebraicGeometry.modulesPullbackSquareIso_paste_app` read as an equality of natural
isomorphisms. -/
theorem modulesPullbackSquareIso_paste (g : X ⟶ Y) (h : Y ⟶ Z) (k : X ⟶ X') (l : Y ⟶ Y')
    (m : Z ⟶ Z') (g' : X' ⟶ Y') (h' : Y' ⟶ Z') (w₁ : g ≫ l = k ≫ g')
    (w₂ : h ≫ m = l ≫ h') (w : (g ≫ h) ≫ m = k ≫ g' ≫ h') :
    Functor.isoWhiskerLeft (Scheme.Modules.pullback m) (Scheme.Modules.pullbackComp g h) ≪≫
        modulesPullbackSquareIso w =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (modulesPullbackSquareIso w₂) (Scheme.Modules.pullback g) ≪≫
          Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft (Scheme.Modules.pullback h')
                (modulesPullbackSquareIso w₁) ≪≫
              (Functor.associator _ _ _).symm ≪≫
                Functor.isoWhiskerRight (Scheme.Modules.pullbackComp g' h')
                  (Scheme.Modules.pullback k) :=
  Iso.ext (NatTrans.ext (funext fun M ↦ by
    simpa using modulesPullbackSquareIso_paste_app g h k l m g' h' w₁ w₂ w M))

end Paste

/-! ### The Frobenius comparison and composition of restrictions -/

section Frobenius

variable (p : ℕ) [Fact p.Prime] {X Y Z : Scheme.{u}} (hX : IsInCharacteristic X p)
  (hY : IsInCharacteristic Y p) (hZ : IsInCharacteristic Z p) (g : X ⟶ Y) (h : Y ⟶ Z)

/-- **The Frobenius comparison is compatible with composition of restrictions, on all sheaves
of modules.** The comparison `AlgebraicGeometry.frobeniusModulesPullbackIso` for the composite
`g ≫ h` is the pasting of the comparisons for `h` and for `g`; this is
`AlgebraicGeometry.modulesPullbackSquareIso_paste` for the two Frobenius naturality squares. -/
theorem frobeniusModulesPullbackIso_comp :
    Functor.isoWhiskerLeft (Scheme.Modules.pullback (absoluteFrobenius Z p hZ))
          (Scheme.Modules.pullbackComp g h) ≪≫
        frobeniusModulesPullbackIso (g ≫ h) p hX hZ =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (frobeniusModulesPullbackIso h p hY hZ)
            (Scheme.Modules.pullback g) ≪≫
          Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft (Scheme.Modules.pullback h)
                (frobeniusModulesPullbackIso g p hX hY) ≪≫
              (Functor.associator _ _ _).symm ≪≫
                Functor.isoWhiskerRight (Scheme.Modules.pullbackComp g h)
                  (Scheme.Modules.pullback (absoluteFrobenius X p hX)) :=
  modulesPullbackSquareIso_paste g h (absoluteFrobenius X p hX) (absoluteFrobenius Y p hY)
    (absoluteFrobenius Z p hZ) g h (absoluteFrobenius_naturality g p hX hY).symm
    (absoluteFrobenius_naturality h p hY hZ).symm
    (absoluteFrobenius_naturality (g ≫ h) p hX hZ).symm

/-- The underlying sheaf of modules of a Frobenius pullback of a vector bundle. -/
@[simp]
lemma frobeniusPullback_obj_obj (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (M : X.Vect) :
    ((frobeniusPullback X p hX).obj M).obj =
      (Scheme.Modules.pullback (absoluteFrobenius X p hX)).obj M.obj :=
  rfl

/-- The underlying morphism of sheaves of modules of a Frobenius pullback of a morphism of
vector bundles. -/
@[simp]
lemma frobeniusPullback_map_hom (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) {M N : X.Vect} (φ : M ⟶ N) :
    ((frobeniusPullback X p hX).map φ).hom =
      (Scheme.Modules.pullback (absoluteFrobenius X p hX)).map φ.hom :=
  rfl

/-- **The Frobenius comparison is compatible with composition of restrictions of vector
bundles.** The comparison `AlgebraicGeometry.frobeniusVectPullbackIso` for the composite
`g ≫ h` is the pasting of the comparisons for `h` and for `g`, so a consumer may rewrite either
composite of structural isomorphisms into the other. This is
`AlgebraicGeometry.frobeniusModulesPullbackIso_comp` transported to the full subcategories of
finite locally free modules. -/
theorem frobeniusVectPullbackIso_comp :
    Functor.isoWhiskerLeft (frobeniusPullback Z p hZ) (Scheme.Vect.pullbackComp g h) ≪≫
        frobeniusVectPullbackIso (g ≫ h) p hX hZ =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (frobeniusVectPullbackIso h p hY hZ) (Scheme.Vect.pullback g) ≪≫
          Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft (Scheme.Vect.pullback h)
                (frobeniusVectPullbackIso g p hX hY) ≪≫
              (Functor.associator _ _ _).symm ≪≫
                Functor.isoWhiskerRight (Scheme.Vect.pullbackComp g h)
                  (frobeniusPullback X p hX) :=
  Iso.ext (NatTrans.ext (funext fun M ↦ ObjectProperty.hom_ext _ (by
    have H := NatTrans.congr_app
      (congrArg Iso.hom (frobeniusModulesPullbackIso_comp p hX hY hZ g h)) M.obj
    simpa using H)))

end Frobenius

end AlgebraicGeometry

end
