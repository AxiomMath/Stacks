module

public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Cotangent.Complex
public import StacksFrontier.Cotangent.SheavesOfRings.CotangentComplex
public import StacksFrontier.Cotangent.SheavesOfRings.InverseImageStandardResolution
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseCotangentComplex

/-!
# The cotangent complex of the sections maps to the sections of the cotangent complex

Let `A ⟶ B` be a homomorphism of sheaves of commutative rings on a site and let `U` be an
object of the site. Taking sections over `U` carries a sheaf of `A`-algebras to an
`A(U)`-algebra. This square of adjunctions — free and forgetful for sheaves of `A`-algebras,
free and forgetful for `A(U)`-algebras — commutes on the forgetful side, while on the free side
there is only a canonical *map* `A(U)[E(U)] ⟶ (A[E])(U)`. Consequently the two free-forgetful
comonads, whose iterates are the two standard resolutions, are compared by a lax (non-invertible)
morphism of comonads, and the standard resolution of the ring map `A(U) → B(U)` maps canonically
to the sections over `U` of the standard resolution of `A ⟶ B`.

Base-changing the differentials along the two augmentations turns that into a map of simplicial
`B(U)`-modules, and the alternating-face-map complex of the latter is the canonical map
`L_{B(U)/A(U)} ⟶ L_{B/A}(U)` of complexes of `B(U)`-modules of Stacks 08SX.

## Main definitions

* `CategoryTheory.Adjunction.comonadLaxHom` is the comparison of the two free-forgetful comonads
  attached to a square of adjunctions whose forgetful half commutes.
* `CategoryTheory.Functor.iterateLaxHom` iterates such a comparison.
* `CategoryTheory.SimplicialObject.homOfFacesAndDegeneracies` assembles degreewise morphisms
  commuting with all faces and degeneracies into a morphism of simplicial objects.
* `CategoryTheory.Sheaf.sectionsAlgebraFunctor` sends a sheaf of `A`-algebras to its
  `A(U)`-algebra of sections over `U`.
* `CategoryTheory.Sheaf.sectionsComonadLax` is the comparison of the two free-forgetful comonads
  in this situation.
* `CategoryTheory.Sheaf.resolutionSectionsComparison` is the resulting morphism of simplicial
  `A(U)`-algebras from the standard resolution of `A(U) → B(U)` to the sections over `U` of the
  standard resolution of `A ⟶ B`.
* `CategoryTheory.Sheaf.cotangentSimplicialComparison` is the induced morphism of simplicial
  `B(U)`-modules `Ω[P'_•⁄A(U)] ⊗ B(U) ⟶ (Ω_{P_•/A} ⊗ B)(U)`.
* `CategoryTheory.Sheaf.cotangentMooreComparison` and
  `CategoryTheory.Sheaf.sectionsCotangentComplexComparison` are the induced maps of
  alternating-face-map complexes and the canonical map `L_{B(U)/A(U)} ⟶ L_{B/A}(U)`.

## Main results

* `CategoryTheory.Adjunction.comonadLaxApp_counit` and
  `CategoryTheory.Adjunction.comonadLaxApp_comul`: the comparison is a morphism of comonads.
* `CategoryTheory.Functor.iterateLaxHom_godementFace` and
  `CategoryTheory.Functor.iterateLaxHom_godementDegeneracy`: the iterated comparison commutes
  with Godement's structure maps, which is what makes the comparison of standard resolutions
  simplicial.
* `CategoryTheory.Sheaf.resolutionSectionsComparison_augmentation`: the comparison of standard
  resolutions is compatible with the two augmentations to `B(U)`.
* `CategoryTheory.Sheaf.cotangentTermComparison_naturality_apply`: the degreewise comparison of
  base-changed differentials commutes with every simplicial operator, which is what makes
  `CategoryTheory.Sheaf.cotangentSimplicialComparison` a morphism of simplicial modules.
* `CategoryTheory.Sheaf.sectionsCotangentComplexComparison_f`: in cohomological degree `-n` the
  canonical map is the degreewise comparison, read through the two canonical degree
  isomorphisms.

## Scope

Remark 08SX makes three assertions: that for every `U` there is a canonical map
`L_{B(U)/A(U)} ⟶ L_{B/A}(U)` of complexes of `B(U)`-modules, that these maps are compatible
with the restriction maps of the site, and that `L_{B/A}` is the sheafification of
`U ↦ L_{B(U)/A(U)}`. This file constructs the map of the first assertion.

## References

* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX)
* [Stacks Project, Tag 08SW](https://stacks.math.columbia.edu/tag/08SW)
* [Stacks Project, Tag 08SR](https://stacks.math.columbia.edu/tag/08SR)
* [Stacks Project, Tag 08PM](https://stacks.math.columbia.edu/tag/08PM)
* [Stacks Project, Tag 0G5M](https://stacks.math.columbia.edu/tag/0G5M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace CategoryTheory

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

section LaxAdjunctionSquare

variable {S : Type u₁} [Category.{v₁} S] {T : Type u₂} [Category.{v₂} T]
  {A : Type u₃} [Category.{v₃} A] {B : Type u₄} [Category.{v₄} B]
  {F : S ⥤ A} {U : A ⥤ S} {F' : T ⥤ B} {U' : B ⥤ T} {L : S ⥤ T} {H : A ⥤ B}

/-- The comparison `F'(U'(H X)) ⟶ H(F(U X))` of the two free-forgetful comonads attached to a
square of adjunctions whose forgetful half commutes, in simplicial degree one: the transpose of
the unit of the top adjunction, read through the comparison `i` of the two forgetful functors.
It is *not* assumed invertible; only the forgetful comparison `i` is. -/
noncomputable def Adjunction.comonadLaxApp (a : F ⊣ U) (b : F' ⊣ U')
    (i : H ⋙ U' ≅ U ⋙ L) (X : A) :
    F'.obj (U'.obj (H.obj X)) ⟶ H.obj (F.obj (U.obj X)) :=
  (b.homEquiv _ _).symm
    (i.hom.app X ≫ L.map (a.unit.app (U.obj X)) ≫ i.inv.app (F.obj (U.obj X)))

/-- The transpose of the comonad comparison. -/
theorem Adjunction.homEquiv_comonadLaxApp (a : F ⊣ U) (b : F' ⊣ U')
    (i : H ⋙ U' ≅ U ⋙ L) (X : A) :
    b.homEquiv _ _ (Adjunction.comonadLaxApp a b i X) =
      i.hom.app X ≫ L.map (a.unit.app (U.obj X)) ≫ i.inv.app (F.obj (U.obj X)) :=
  (b.homEquiv _ _).apply_symm_apply _

/-- The comonad comparison, transposed through the unit of the bottom adjunction. -/
theorem Adjunction.unit_comp_comonadLaxApp (a : F ⊣ U) (b : F' ⊣ U')
    (i : H ⋙ U' ≅ U ⋙ L) (X : A) :
    b.unit.app (U'.obj (H.obj X)) ≫ U'.map (Adjunction.comonadLaxApp a b i X) =
      i.hom.app X ≫ L.map (a.unit.app (U.obj X)) ≫ i.inv.app (F.obj (U.obj X)) :=
  Adjunction.homEquiv_comonadLaxApp a b i X

/-- The comparison of the two free-forgetful comonads attached to a square of adjunctions whose
forgetful half commutes. -/
noncomputable def Adjunction.comonadLaxHom (a : F ⊣ U) (b : F' ⊣ U')
    (i : H ⋙ U' ≅ U ⋙ L) : H ⋙ (U' ⋙ F') ⟶ (U ⋙ F) ⋙ H where
  app X := Adjunction.comonadLaxApp a b i X
  naturality X Y k := by
    apply (b.homEquiv _ _).injective
    change b.homEquiv _ _ (F'.map (U'.map (H.map k)) ≫ Adjunction.comonadLaxApp a b i Y) =
      b.homEquiv _ _ (Adjunction.comonadLaxApp a b i X ≫ H.map (F.map (U.map k)))
    have h1 : U'.map (H.map k) ≫ i.hom.app Y = i.hom.app X ≫ L.map (U.map k) :=
      i.hom.naturality k
    have h2 : L.map (U.map (F.map (U.map k))) ≫ i.inv.app (F.obj (U.obj Y)) =
        i.inv.app (F.obj (U.obj X)) ≫ U'.map (H.map (F.map (U.map k))) :=
      i.inv.naturality (F.map (U.map k))
    have h3 : a.unit.app (U.obj X) ≫ U.map (F.map (U.map k)) =
        U.map k ≫ a.unit.app (U.obj Y) := a.unit_naturality (U.map k)
    have h4 : L.map (U.map k) ≫ L.map (a.unit.app (U.obj Y)) =
        L.map (a.unit.app (U.obj X)) ≫ L.map (U.map (F.map (U.map k))) := by
      rw [← L.map_comp, ← L.map_comp, h3]
    rw [b.homEquiv_naturality_left, b.homEquiv_naturality_right,
      Adjunction.homEquiv_comonadLaxApp, Adjunction.homEquiv_comonadLaxApp]
    simp only [Category.assoc]
    rw [reassoc_of% h1, ← h2, reassoc_of% h4]

/-- The comonad comparison is compatible with the two counits. -/
theorem Adjunction.comonadLaxApp_counit (a : F ⊣ U) (b : F' ⊣ U')
    (i : H ⋙ U' ≅ U ⋙ L) (X : A) :
    Adjunction.comonadLaxApp a b i X ≫ H.map (a.counit.app X) = b.counit.app (H.obj X) := by
  apply (b.homEquiv _ _).injective
  have h2 : L.map (U.map (a.counit.app X)) ≫ i.inv.app X =
      i.inv.app (F.obj (U.obj X)) ≫ U'.map (H.map (a.counit.app X)) :=
    i.inv.naturality (a.counit.app X)
  have h3 : L.map (a.unit.app (U.obj X)) ≫ L.map (U.map (a.counit.app X)) = 𝟙 _ := by
    rw [← L.map_comp, a.right_triangle_components]
    simp
  rw [b.homEquiv_naturality_right, Adjunction.homEquiv_comonadLaxApp]
  simp only [Category.assoc]
  rw [← h2, reassoc_of% h3]
  simp [Adjunction.homEquiv_apply]

/-- The comonad comparison is compatible with the two comultiplications. -/
theorem Adjunction.comonadLaxApp_comul (a : F ⊣ U) (b : F' ⊣ U')
    (i : H ⋙ U' ≅ U ⋙ L) (X : A) :
    Adjunction.comonadLaxApp a b i X ≫ H.map (F.map (a.unit.app (U.obj X))) =
      F'.map (b.unit.app (U'.obj (H.obj X))) ≫
        F'.map (U'.map (Adjunction.comonadLaxApp a b i X)) ≫
          Adjunction.comonadLaxApp a b i (F.obj (U.obj X)) := by
  rw [← F'.map_comp_assoc]
  apply (b.homEquiv _ _).injective
  have h2 : L.map (U.map (F.map (a.unit.app (U.obj X)))) ≫
        i.inv.app (F.obj (U.obj (F.obj (U.obj X)))) =
      i.inv.app (F.obj (U.obj X)) ≫ U'.map (H.map (F.map (a.unit.app (U.obj X)))) :=
    i.inv.naturality (F.map (a.unit.app (U.obj X)))
  have h3 : a.unit.app (U.obj X) ≫ U.map (F.map (a.unit.app (U.obj X))) =
      a.unit.app (U.obj X) ≫ a.unit.app (U.obj (F.obj (U.obj X))) :=
    a.unit_naturality (a.unit.app (U.obj X))
  have h4 : L.map (a.unit.app (U.obj X)) ≫
        L.map (U.map (F.map (a.unit.app (U.obj X)))) =
      L.map (a.unit.app (U.obj X)) ≫ L.map (a.unit.app (U.obj (F.obj (U.obj X)))) := by
    rw [← L.map_comp, ← L.map_comp, h3]
  rw [b.homEquiv_naturality_right, b.homEquiv_naturality_left,
    Adjunction.homEquiv_comonadLaxApp, Adjunction.unit_comp_comonadLaxApp]
  dsimp only [Functor.comp_obj]
  rw [Adjunction.homEquiv_comonadLaxApp]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_app_assoc, ← h2, reassoc_of% h4]

end LaxAdjunctionSquare

section Iterate

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

/-- A comparison `H ⋙ G' ⟶ G ⋙ H` of commuting endofunctors, iterated `n` times. Unlike
`CategoryTheory.Functor.iterateCompIso` the comparison is not assumed invertible. -/
def Functor.iterateLaxHom {G : A ⥤ A} {G' : B ⥤ B} {H : A ⥤ B}
    (l : H ⋙ G' ⟶ G ⋙ H) : (n : ℕ) → (H ⋙ G'.iterate n ⟶ G.iterate n ⋙ H)
  | 0 => 𝟙 H
  | n + 1 => Functor.whiskerRight (Functor.iterateLaxHom l n) G' ≫
      Functor.whiskerLeft (G.iterate n) l

/-- The first iterate of a comparison is the comparison itself. -/
@[simp]
theorem Functor.iterateLaxHom_one {G : A ⥤ A} {G' : B ⥤ B} {H : A ⥤ B}
    (l : H ⋙ G' ⟶ G ⋙ H) (X : A) : (Functor.iterateLaxHom l 1).app X = l.app X := by
  change G'.map (𝟙 (H.obj X)) ≫ l.app X = l.app X
  simp

/-- The iterated comparison commutes with Godement's face maps. -/
theorem Functor.iterateLaxHom_godementFace {G : A ⥤ A} {G' : B ⥤ B} {H : A ⥤ B}
    (l : H ⋙ G' ⟶ G ⋙ H) (ε : G ⟶ 𝟭 A) (ε' : G' ⟶ 𝟭 B)
    (hε : ∀ X, l.app X ≫ H.map (ε.app X) = ε'.app (H.obj X))
    (n : ℕ) (j : Fin (n + 1)) (X : A) :
    (Godement.face ε' n j).app (H.obj X) ≫ (Functor.iterateLaxHom l n).app X =
      (Functor.iterateLaxHom l (n + 1)).app X ≫ H.map ((Godement.face ε n j).app X) := by
  induction n with
  | zero =>
    simpa [Godement.face, Functor.iterateLaxHom, Functor.iterate] using (hε X).symm
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Godement.Prep.face_zero, Functor.whiskerLeft_app]
      change ε'.app ((G'.iterate (n + 1)).obj (H.obj X)) ≫ _ =
        (G'.map ((Functor.iterateLaxHom l (n + 1)).app X) ≫
          l.app ((G.iterate (n + 1)).obj X)) ≫ _
      rw [Category.assoc, hε ((G.iterate (n + 1)).obj X)]
      have hn := ε'.naturality ((Functor.iterateLaxHom l (n + 1)).app X)
      dsimp only [Functor.id_map, Functor.comp_obj] at hn
      exact hn.symm
    · simp only [Godement.Prep.face_succ, Functor.whiskerRight_app]
      change G'.map ((Godement.face ε' n j).app (H.obj X)) ≫
          (G'.map ((Functor.iterateLaxHom l n).app X) ≫ l.app ((G.iterate n).obj X)) =
        (G'.map ((Functor.iterateLaxHom l (n + 1)).app X) ≫
            l.app ((G.iterate (n + 1)).obj X)) ≫
          H.map (G.map ((Godement.face ε n j).app X))
      rw [← Category.assoc, ← G'.map_comp, ih j, G'.map_comp, Category.assoc,
        Category.assoc]
      have hn := l.naturality ((Godement.face ε n j).app X)
      dsimp only [Functor.comp_map, Functor.comp_obj] at hn
      rw [hn]

/-- The iterated comparison commutes with Godement's degeneracy maps. -/
theorem Functor.iterateLaxHom_godementDegeneracy {G : A ⥤ A} {G' : B ⥤ B} {H : A ⥤ B}
    (l : H ⋙ G' ⟶ G ⋙ H) (δ : G ⟶ G ⋙ G) (δ' : G' ⟶ G' ⋙ G')
    (hδ : ∀ X, δ'.app (H.obj X) ≫ G'.map (l.app X) ≫ l.app (G.obj X) =
      l.app X ≫ H.map (δ.app X))
    (n : ℕ) (j : Fin (n + 1)) (X : A) :
    (Godement.degeneracy δ' n j).app (H.obj X) ≫ (Functor.iterateLaxHom l (n + 2)).app X =
      (Functor.iterateLaxHom l (n + 1)).app X ≫
        H.map ((Godement.degeneracy δ n j).app X) := by
  induction n with
  | zero =>
    simpa [Godement.degeneracy, Functor.iterateLaxHom, Functor.iterate] using hδ X
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Godement.Prep.degeneracy_zero, Functor.whiskerLeft_app]
      change δ'.app ((G'.iterate (n + 1)).obj (H.obj X)) ≫
          (G'.map (G'.map ((Functor.iterateLaxHom l (n + 1)).app X) ≫
            l.app ((G.iterate (n + 1)).obj X)) ≫
              l.app (G.obj ((G.iterate (n + 1)).obj X))) =
        (G'.map ((Functor.iterateLaxHom l (n + 1)).app X) ≫
            l.app ((G.iterate (n + 1)).obj X)) ≫ _
      have hn := δ'.naturality ((Functor.iterateLaxHom l (n + 1)).app X)
      dsimp only [Functor.comp_map, Functor.comp_obj] at hn
      rw [G'.map_comp]
      simp only [Category.assoc]
      rw [← Category.assoc, ← hn]
      simp only [Category.assoc]
      rw [hδ ((G.iterate (n + 1)).obj X)]
    · simp only [Godement.Prep.degeneracy_succ, Functor.whiskerRight_app]
      change G'.map ((Godement.degeneracy δ' n j).app (H.obj X)) ≫
          (G'.map ((Functor.iterateLaxHom l (n + 2)).app X) ≫
            l.app ((G.iterate (n + 2)).obj X)) =
        (G'.map ((Functor.iterateLaxHom l (n + 1)).app X) ≫
            l.app ((G.iterate (n + 1)).obj X)) ≫
          H.map (G.map ((Godement.degeneracy δ n j).app X))
      rw [← Category.assoc, ← G'.map_comp, ih j, G'.map_comp, Category.assoc,
        Category.assoc]
      have hn := l.naturality ((Godement.degeneracy δ n j).app X)
      dsimp only [Functor.comp_map, Functor.comp_obj] at hn
      rw [hn]

end Iterate

section SimplicialHom

variable {D : Type u₁} [Category.{v₁} D]

/-- Degreewise morphisms commuting with every face and every degeneracy map assemble into a
morphism of simplicial objects, the faces and degeneracies generating every simplex map. This is
the lax counterpart of `CategoryTheory.SimplicialObject.isoOfFacesAndDegeneracies`. -/
def SimplicialObject.homOfFacesAndDegeneracies {X Y : SimplicialObject D}
    (e : ∀ n, X.obj (op ⦋n⦌) ⟶ Y.obj (op ⦋n⦌))
    (hδ : ∀ n (j : Fin (n + 2)), X.δ j ≫ e n = e (n + 1) ≫ Y.δ j)
    (hσ : ∀ n (j : Fin (n + 1)), X.σ j ≫ e (n + 1) = e n ≫ Y.σ j) :
    X ⟶ Y := by
  let W : MorphismProperty SimplexCategory := fun {a b} g =>
    X.map g.op ≫ e a.len = e b.len ≫ Y.map g.op
  have : W.IsMultiplicative :=
    { id_mem := fun a => by simp [W]
      comp_mem := fun g h hg hh => by
        dsimp only [W] at *
        simp only [op_comp, Functor.map_comp, Category.assoc]
        rw [hg, ← Category.assoc, hh, Category.assoc] }
  have hw : W = ⊤ := SimplexCategory.morphismProperty_eq_top W (fun j => hδ _ j) (fun j => hσ _ j)
  exact { app := fun n => e n.unop.len, naturality := fun _ _ g => (hw ▸ trivial : W g.unop) }

/-- The degree-`n` component of the morphism of simplicial objects built from the maps `e` is
`e n`. -/
@[simp]
theorem SimplicialObject.homOfFacesAndDegeneracies_app {X Y : SimplicialObject D}
    (e : ∀ n, X.obj (op ⦋n⦌) ⟶ Y.obj (op ⦋n⦌))
    (hδ : ∀ n (j : Fin (n + 2)), X.δ j ≫ e n = e (n + 1) ≫ Y.δ j)
    (hσ : ∀ n (j : Fin (n + 1)), X.σ j ≫ e (n + 1) = e n ≫ Y.σ j) (n : ℕ) :
    (SimplicialObject.homOfFacesAndDegeneracies e hδ hσ).app (op ⦋n⦌) = e n :=
  rfl

end SimplicialHom

section Conjugate

variable {D₁ : Type u₁} [Category.{v₁} D₁] {D₂ : Type u₂} [Category.{v₂} D₂]

/-- A square commuting between two systems transported along equalities of objects commutes
after the transport. -/
theorem conjugate_square (H : D₁ ⥤ D₂) {p₁ p₂ q₁ q₂ : D₂} {x₁ x₂ y₁ y₂ : D₁}
    (h₁ : p₁ = q₁) (h₂ : p₂ = q₂) (k₁ : x₁ = y₁) (k₂ : x₂ = y₂)
    (dq : q₂ ⟶ q₁) (dy : y₂ ⟶ y₁) (m₁ : q₁ ⟶ H.obj y₁) (m₂ : q₂ ⟶ H.obj y₂)
    (hm : dq ≫ m₁ = m₂ ≫ H.map dy) :
    (eqToHom h₂ ≫ dq ≫ eqToHom h₁.symm) ≫
        (eqToHom h₁ ≫ m₁ ≫ H.map (eqToHom k₁.symm)) =
      (eqToHom h₂ ≫ m₂ ≫ H.map (eqToHom k₂.symm)) ≫
        H.map (eqToHom k₂ ≫ dy ≫ eqToHom k₁.symm) := by
  subst h₁ h₂ k₁ k₂
  simp [hm]

/-- A triangle commuting between two systems transported along equalities of objects commutes
after the transport. -/
theorem conjugate_triangle (H : D₁ ⥤ D₂) {p q : D₂} {x y Z : D₁}
    (h : p = q) (k : x = y) (m : q ⟶ H.obj y) (e : y ⟶ Z) (e' : q ⟶ H.obj Z)
    (hm : m ≫ H.map e = e') :
    (eqToHom h ≫ m ≫ H.map (eqToHom k.symm)) ≫ H.map (eqToHom k ≫ e) =
      (eqToHom h ≫ e') ≫ 𝟙 (H.obj Z) := by
  subst h k
  simp [hm]

end Conjugate

section SimplicialConst

variable {D : Type u₁} [Category.{v₁} D]

/-- A morphism of simplicial objects compatible in degree zero with two morphisms to constant
objects is compatible with them in every degree. This is the lax counterpart of
`CategoryTheory.SimplicialObject.hom_comp_toConst_of_zero`. -/
theorem SimplicialObject.hom_comp_toConst {X Y : SimplicialObject D} {P Q : D}
    (a : X ⟶ (SimplicialObject.const D).obj P)
    (b : Y ⟶ (SimplicialObject.const D).obj Q) (e : X ⟶ Y) (c : P ⟶ Q)
    (h₀ : e.app (op ⦋0⦌) ≫ b.app (op ⦋0⦌) = a.app (op ⦋0⦌) ≫ c)
    (n : ℕ) : e.app (op ⦋n⦌) ≫ b.app (op ⦋n⦌) = a.app (op ⦋n⦌) ≫ c := by
  induction n with
  | zero => exact h₀
  | succ n ih =>
    have key : ∀ {Z : SimplicialObject D} {R : D} (c : Z ⟶ (SimplicialObject.const D).obj R),
        Z.map (SimplexCategory.δ (0 : Fin (n + 2))).op ≫ c.app (op ⦋n⦌) = c.app (op ⦋n + 1⦌) :=
      fun c => (c.naturality (SimplexCategory.δ (0 : Fin (n + 2))).op).trans (Category.comp_id _)
    rw [← key b, ← Category.assoc, ← e.naturality, Category.assoc, ih, ← Category.assoc, key a]

end SimplicialConst

end CategoryTheory

namespace CommAlgCat

universe u₇ v₇

open scoped ChangeOfRings TensorProduct

/-- The `Pₙ`-linear map `Ω[Pₙ⁄A] → N` attached to a derivation of `Pₙ` with values in a
`B`-module `N`, read as a map into the restriction of scalars of `N` along the augmentation; it
is adjoint to `cotangentTermDesc`. -/
noncomputable def cotangentTermDescAdjoint (A : Type u₇) [CommRing A]
    (B : CommAlgCat.{max u₇ v₇} A) (n : SimplexCategoryᵒᵖ) (N : ModuleCat.{max u₇ v₇} B)
    (d : (standardResolution A B).left.obj n →+ N)
    (hmul : ∀ x y, d (x * y) =
      standardResolutionAugmentationHom A B n x • d y +
        standardResolutionAugmentationHom A B n y • d x)
    (hbase : ∀ a : A, d (algebraMap A ((standardResolution A B).left.obj n) a) = 0) :
    ModuleCat.of ((standardResolution A B).left.obj n)
        (KaehlerDifferential A ((standardResolution A B).left.obj n)) ⟶
      (ModuleCat.restrictScalars (standardResolutionAugmentationHom A B n)).obj N := by
  let P := (standardResolution A B).left.obj n
  let ε := standardResolutionAugmentationHom A B n
  let M := (ModuleCat.restrictScalars ε).obj N
  letI : Module A M := Module.compHom M (algebraMap A P)
  letI : IsScalarTower A P M := ⟨fun a p x => by
    change (a • p) • x = (algebraMap A P a) • (p • x)
    rw [Algebra.smul_def, mul_smul]⟩
  let D : Derivation A P M :=
    { toFun := d
      map_add' := d.map_add
      map_smul' := fun a p => by
        change d (a • p) = ε (algebraMap A P a) • d p
        rw [Algebra.smul_def, hmul, hbase, smul_zero, add_zero]
      map_one_eq_zero' := (by simpa using hbase 1 : d 1 = 0)
      leibniz' := hmul }
  exact ModuleCat.ofHom (X := ModuleCat.of P (KaehlerDifferential A P)) (Y := M)
    D.liftKaehlerDifferential

/-- `cotangentTermDescAdjoint` sends the differential `d p` to `d p`. -/
theorem cotangentTermDescAdjoint_D (A : Type u₇) [CommRing A]
    (B : CommAlgCat.{max u₇ v₇} A) (n : SimplexCategoryᵒᵖ) (N : ModuleCat.{max u₇ v₇} B)
    (d : (standardResolution A B).left.obj n →+ N)
    (hmul : ∀ x y, d (x * y) =
      standardResolutionAugmentationHom A B n x • d y +
        standardResolutionAugmentationHom A B n y • d x)
    (hbase : ∀ a : A, d (algebraMap A ((standardResolution A B).left.obj n) a) = 0)
    (p : (standardResolution A B).left.obj n) :
    cotangentTermDescAdjoint A B n N d hmul hbase
      (KaehlerDifferential.D A ((standardResolution A B).left.obj n) p) = d p := by
  let P := (standardResolution A B).left.obj n
  let M := (ModuleCat.restrictScalars (standardResolutionAugmentationHom A B n)).obj N
  let _ : Module A M := Module.compHom M (algebraMap A P)
  let _ : IsScalarTower A P M := ⟨fun a p x => by
    change (a • p) • x = (algebraMap A P a) • (p • x)
    rw [Algebra.smul_def, mul_smul]⟩
  unfold cotangentTermDescAdjoint
  exact Derivation.liftKaehlerDifferential_comp_D _ p

/-- The `B`-linear map out of the base-changed differentials `B ⊗[Pₙ] Ω[Pₙ⁄A]` determined by a
derivation of `Pₙ` with values in a `B`-module. -/
noncomputable def cotangentTermDesc (A : Type u₇) [CommRing A] (B : CommAlgCat.{max u₇ v₇} A)
    (n : SimplexCategoryᵒᵖ) (N : ModuleCat.{max u₇ v₇} B)
    (d : (standardResolution A B).left.obj n →+ N)
    (hmul : ∀ x y, d (x * y) =
      standardResolutionAugmentationHom A B n x • d y +
        standardResolutionAugmentationHom A B n y • d x)
    (hbase : ∀ a : A, d (algebraMap A ((standardResolution A B).left.obj n) a) = 0) :
    cotangentTerm A B n ⟶ N :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (standardResolutionAugmentationHom A B n) (cotangentTermDescAdjoint A B n N d hmul hbase)

/-- `cotangentTermDesc` sends the pure differential `1 ⊗ d p` to `d p`. -/
theorem cotangentTermDesc_differential (A : Type u₇) [CommRing A]
    (B : CommAlgCat.{max u₇ v₇} A)
    (n : SimplexCategoryᵒᵖ) (N : ModuleCat.{max u₇ v₇} B)
    (d : (standardResolution A B).left.obj n →+ N)
    (hmul : ∀ x y, d (x * y) =
      standardResolutionAugmentationHom A B n x • d y +
        standardResolutionAugmentationHom A B n y • d x)
    (hbase : ∀ a : A, d (algebraMap A ((standardResolution A B).left.obj n) a) = 0)
    (p : (standardResolution A B).left.obj n) :
    cotangentTermDesc A B n N d hmul hbase (cotangentTermDifferential A B n p) = d p :=
  (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul
    (standardResolutionAugmentationHom A B n) (cotangentTermDescAdjoint A B n N d hmul hbase)
    (1 : B) (KaehlerDifferential.D A ((standardResolution A B).left.obj n) p)).trans
      (by rw [one_smul, cotangentTermDescAdjoint_D])

end CommAlgCat

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-- Sections over `U` of a sheaf of sets. -/
noncomputable abbrev sectionsOfSets (U : Cᵒᵖ) :
    Sheaf J (Type (max u v w)) ⥤ Type (max u v w) :=
  sheafToPresheaf J (Type (max u v w)) ⋙ (evaluation Cᵒᵖ (Type (max u v w))).obj U

/-- Sections over `U` of a sheaf of `A`-algebras, as an algebra over the sections `A(U)`. -/
noncomputable def sectionsAlgebraFunctor (U : Cᵒᵖ) :
    Under A ⥤ CommAlgCat.{max u v w} (A.obj.obj U) where
  obj X :=
    letI : Algebra (A.obj.obj U) (X.right.obj.obj U) := (X.hom.hom.app U).hom.toAlgebra
    CommAlgCat.of (A.obj.obj U) (X.right.obj.obj U)
  map {X Y} g :=
    letI : Algebra (A.obj.obj U) (X.right.obj.obj U) := (X.hom.hom.app U).hom.toAlgebra
    letI : Algebra (A.obj.obj U) (Y.right.obj.obj U) := (Y.hom.hom.app U).hom.toAlgebra
    CommAlgCat.ofHom
      { __ := (g.right.hom.app U).hom
        commutes' := fun a =>
          congrArg (fun k : A ⟶ Y.right => (k.hom.app U).hom a) (Under.w g) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The sections of a sheaf of `A`-algebras over `U` have the sections of the underlying sheaf
of sets as underlying set: taking sections over `U` commutes with the forgetful functors. -/
noncomputable def sectionsForgetIso (U : Cᵒᵖ) :
    sectionsAlgebraFunctor J U (A := A) ⋙ forget (CommAlgCat.{max u v w} (A.obj.obj U)) ≅
      forgetAlgebraSheaf.{v, u, w} J A ⋙ sectionsOfSets J U :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- The sections of `B` over `U`, as an `A(U)`-algebra, are the sections of the standard
resolution's augmentation point. -/
theorem sectionsAlgebraFunctor_obj_mk (U : Cᵒᵖ) :
    (sectionsAlgebraFunctor J U).obj (Under.mk f) = sectionsAlgebra J f U :=
  rfl

/-- The free-forgetful comonad on `A(U)`-algebras, whose iterates are the terms of the standard
resolution of a ring map. -/
noncomputable abbrev sectionsComonad (U : Cᵒᵖ) :
    Comonad (CommAlgCat.{max u v w} (A.obj.obj U)) :=
  CommAlgCat.polynomialComonad.{max u v w, max u v w} (A.obj.obj U)

/-- Over an object `U` of the site, the free `A(U)`-algebra on the sections of a sheaf of
`A`-algebras maps canonically to the sections of the free `A`-algebra sheaf on it; this is the lax
comparison of the two free-forgetful comonads whose iterates are the two standard resolutions. -/
noncomputable def sectionsComonadLax (U : Cᵒᵖ) :
    sectionsAlgebraFunctor J U (A := A) ⋙
        ((sectionsComonad J (A := A) U : Comonad (CommAlgCat.{max u v w} (A.obj.obj U))) :
          CommAlgCat.{max u v w} (A.obj.obj U) ⥤ CommAlgCat.{max u v w} (A.obj.obj U)) ⟶
      ((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) : Under A ⥤ Under A) ⋙
        sectionsAlgebraFunctor J U :=
  Adjunction.comonadLaxHom (freeAlgebraSheafAdjunction.{v, u, w} J A)
    (CommAlgCat.adj.{max u v w, max u v w} (A.obj.obj U)) (sectionsForgetIso J U)

/-- The comonad comparison is compatible with the two counits. -/
theorem sectionsComonadLax_counit (U : Cᵒᵖ) (X : Under A) :
    (sectionsComonadLax J U).app X ≫
        (sectionsAlgebraFunctor J U).map
          ((standardResolutionComonad.{v, u, w} J A).ε.app X) =
      (sectionsComonad J (A := A) U).ε.app ((sectionsAlgebraFunctor J U).obj X) :=
  Adjunction.comonadLaxApp_counit (freeAlgebraSheafAdjunction.{v, u, w} J A)
    (CommAlgCat.adj.{max u v w, max u v w} (A.obj.obj U)) (sectionsForgetIso J U) X

/-- The comonad comparison is compatible with the two comultiplications. -/
theorem sectionsComonadLax_comul (U : Cᵒᵖ) (X : Under A) :
    (sectionsComonad J (A := A) U).δ.app ((sectionsAlgebraFunctor J U).obj X) ≫
        ((sectionsComonad J (A := A) U : Comonad (CommAlgCat.{max u v w} (A.obj.obj U))) :
            CommAlgCat.{max u v w} (A.obj.obj U) ⥤
              CommAlgCat.{max u v w} (A.obj.obj U)).map ((sectionsComonadLax J U).app X) ≫
          (sectionsComonadLax J U).app
            (((standardResolutionComonad.{v, u, w} J A : Comonad (Under A)) :
              Under A ⥤ Under A).obj X) =
      (sectionsComonadLax J U).app X ≫
        (sectionsAlgebraFunctor J U).map
          ((standardResolutionComonad.{v, u, w} J A).δ.app X) :=
  (Adjunction.comonadLaxApp_comul (freeAlgebraSheafAdjunction.{v, u, w} J A)
    (CommAlgCat.adj.{max u v w, max u v w} (A.obj.obj U)) (sectionsForgetIso J U) X).symm

/-- The comparison `P'_n ⟶ P_n(U)` of the degree-`n` term of the standard resolution of the ring
map `A(U) → B(U)` with the sections over `U` of the degree-`n` term of the standard resolution
of `A ⟶ B`: the `(n + 1)`-fold iterate of the comonad comparison, read through the
identifications of both terms with iterates of their comonads. -/
noncomputable def resolutionSectionsComparisonApp (U : Cᵒᵖ) (n : ℕ) :
    (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U)).left.obj (op ⦋n⦌) ⟶
      (sectionsAlgebraFunctor J U).obj ((standardResolution J f).left.obj (op ⦋n⦌)) :=
  eqToHom (CommAlgCat.standardResolution_obj.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U) n) ≫
    (Functor.iterateLaxHom (sectionsComonadLax J U) (n + 1)).app (Under.mk f) ≫
      (sectionsAlgebraFunctor J U).map
        (eqToHom (standardResolution_obj.{v, u, w} J f n).symm)

/-- The iterated comonad comparison commutes with Godement's face maps, at the standard
resolution of `A ⟶ B`. -/
@[reassoc]
private theorem godementFace_comp_iterateLaxHom (U : Cᵒᵖ) (n : ℕ) (j : Fin (n + 2)) :
    (Godement.face
        (CommAlgCat.polynomialComonad.{max u v w, max u v w} (A.obj.obj U)).ε (n + 1) j).app
          (sectionsAlgebra J f U) ≫
        (Functor.iterateLaxHom (sectionsComonadLax J U) (n + 1)).app (Under.mk f) =
      (Functor.iterateLaxHom (sectionsComonadLax J U) (n + 1 + 1)).app (Under.mk f) ≫
        (sectionsAlgebraFunctor J U).map
          ((Godement.face (standardResolutionComonad.{v, u, w} J A).ε (n + 1) j).app
            (Under.mk f)) :=
  Functor.iterateLaxHom_godementFace (sectionsComonadLax J U)
    (standardResolutionComonad.{v, u, w} J A).ε (sectionsComonad J (A := A) U).ε
    (sectionsComonadLax_counit J U) (n + 1) j (Under.mk f)

/-- The iterated comonad comparison commutes with Godement's degeneracy maps, at the standard
resolution of `A ⟶ B`. -/
@[reassoc]
private theorem godementDegeneracy_comp_iterateLaxHom (U : Cᵒᵖ) (n : ℕ) (j : Fin (n + 1)) :
    (Godement.degeneracy
        (CommAlgCat.polynomialComonad.{max u v w, max u v w} (A.obj.obj U)).δ n j).app
          (sectionsAlgebra J f U) ≫
        (Functor.iterateLaxHom (sectionsComonadLax J U) (n + 2)).app (Under.mk f) =
      (Functor.iterateLaxHom (sectionsComonadLax J U) (n + 1)).app (Under.mk f) ≫
        (sectionsAlgebraFunctor J U).map
          ((Godement.degeneracy (standardResolutionComonad.{v, u, w} J A).δ n j).app
            (Under.mk f)) :=
  Functor.iterateLaxHom_godementDegeneracy (sectionsComonadLax J U)
    (standardResolutionComonad.{v, u, w} J A).δ (sectionsComonad J (A := A) U).δ
    (sectionsComonadLax_comul J U) n j (Under.mk f)

/-- The comparison of standard resolutions commutes with every face map. -/
theorem resolutionSectionsComparisonApp_face (U : Cᵒᵖ) (n : ℕ) (j : Fin (n + 2)) :
    (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
          (sectionsAlgebra J f U)).left.δ j ≫ resolutionSectionsComparisonApp J f U n =
      resolutionSectionsComparisonApp J f U (n + 1) ≫
        (sectionsAlgebraFunctor J U).map ((standardResolution J f).left.δ j) := by
  rw [CommAlgCat.standardResolution_face.{max u v w, max u v w},
    standardResolution_delta J f n j]
  exact conjugate_square (sectionsAlgebraFunctor J U)
    (CommAlgCat.standardResolution_obj.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U) n)
    (CommAlgCat.standardResolution_obj.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U) (n + 1))
    (standardResolution_obj.{v, u, w} J f n) (standardResolution_obj.{v, u, w} J f (n + 1))
    _ _ _ _ (godementFace_comp_iterateLaxHom J f U n j)

/-- The comparison of standard resolutions commutes with every degeneracy map. -/
theorem resolutionSectionsComparisonApp_degeneracy (U : Cᵒᵖ) (n : ℕ) (j : Fin (n + 1)) :
    (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
          (sectionsAlgebra J f U)).left.σ j ≫ resolutionSectionsComparisonApp J f U (n + 1) =
      resolutionSectionsComparisonApp J f U n ≫
        (sectionsAlgebraFunctor J U).map ((standardResolution J f).left.σ j) := by
  rw [CommAlgCat.standardResolution_degeneracy.{max u v w, max u v w},
    standardResolution_sigma J f n j]
  exact conjugate_square (sectionsAlgebraFunctor J U)
    (CommAlgCat.standardResolution_obj.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U) (n + 1))
    (CommAlgCat.standardResolution_obj.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U) n)
    (standardResolution_obj.{v, u, w} J f (n + 1)) (standardResolution_obj.{v, u, w} J f n)
    _ _ _ _ (godementDegeneracy_comp_iterateLaxHom J f U n j)

/-- In degree zero the augmentation of the standard resolution of `A(U) → B(U)` is the counit
of the polynomial comonad. -/
private theorem ringAugmentation_zero (U : Cᵒᵖ) :
    (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U)).hom.app (op ⦋0⦌) =
      eqToHom (CommAlgCat.standardResolution_obj.{max u v w, max u v w} (A.obj.obj U)
          (sectionsAlgebra J f U) 0) ≫
        (CommAlgCat.polynomialComonad.{max u v w, max u v w} (A.obj.obj U)).ε.app
          (sectionsAlgebra J f U) := by
  change (((CommAlgCat.standardEndofunctor.{max u v w, max u v w} (A.obj.obj U)).hom.app
      (op ⦋0⦌)).app (sectionsAlgebra J f U) ≫ 𝟙 _) ≫
      eqToHom (congrArg
        (fun F : CommAlgCat.{max u v w} (A.obj.obj U) ⥤ CommAlgCat.{max u v w} (A.obj.obj U) =>
          F.obj (sectionsAlgebra J f U))
        (CommAlgCat.standardEndofunctor_right.{max u v w, max u v w} (A.obj.obj U))) = _
  rw [Category.comp_id,
    CommAlgCat.standardEndofunctor_augmentation.{max u v w, max u v w} (A.obj.obj U)]
  simp only [NatTrans.comp_app, eqToHom_app, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]
  rfl

/-- The first iterate of the comonad comparison is the comparison itself, and is compatible with
the two counits. -/
private theorem iterateLaxHom_one_counit (U : Cᵒᵖ) :
    (Functor.iterateLaxHom (sectionsComonadLax J U) 1).app (Under.mk f) ≫
        (sectionsAlgebraFunctor J U).map
          ((standardResolutionComonad.{v, u, w} J A).ε.app (Under.mk f)) =
      (CommAlgCat.polynomialComonad.{max u v w, max u v w} (A.obj.obj U)).ε.app
        (sectionsAlgebra J f U) := by
  rw [Functor.iterateLaxHom_one]
  exact sectionsComonadLax_counit J U (Under.mk f)

/-- The standard resolution of the ring map `A(U) → B(U)` maps canonically to the sections over `U`
of the standard resolution of `A ⟶ B`, as simplicial `A(U)`-algebras. -/
noncomputable def resolutionSectionsComparison (U : Cᵒᵖ) :
    (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U)).left ⟶
      (standardResolution J f).left ⋙ sectionsAlgebraFunctor J U :=
  SimplicialObject.homOfFacesAndDegeneracies (resolutionSectionsComparisonApp J f U)
    (resolutionSectionsComparisonApp_face J f U)
    (resolutionSectionsComparisonApp_degeneracy J f U)

/-- The comparison of standard resolutions is compatible with the two augmentations to `B(U)`,
in every simplicial degree. -/
theorem resolutionSectionsComparison_augmentation (U : Cᵒᵖ) (n : ℕ) :
    resolutionSectionsComparisonApp J f U n ≫
        (sectionsAlgebraFunctor J U).map ((standardResolution J f).hom.app (op ⦋n⦌)) =
      (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U)).hom.app (op ⦋n⦌) := by
  have h0 : resolutionSectionsComparisonApp J f U 0 ≫
      (sectionsAlgebraFunctor J U).map ((standardResolution J f).hom.app (op ⦋0⦌)) =
      (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
          (sectionsAlgebra J f U)).hom.app (op ⦋0⦌) ≫ 𝟙 (sectionsAlgebra J f U) := by
    rw [standardResolution_augmentation_app_zero J f, ringAugmentation_zero]
    exact conjugate_triangle (sectionsAlgebraFunctor J U)
      (CommAlgCat.standardResolution_obj.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U) 0)
      (standardResolution_obj.{v, u, w} J f 0) _ _ _ (iterateLaxHom_one_counit J f U)
  exact (SimplicialObject.hom_comp_toConst
    (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).hom
    (SimplicialObject.mapToConst (sectionsAlgebraFunctor J U) (standardResolution J f).hom)
    (resolutionSectionsComparison J f U) (𝟙 (sectionsAlgebra J f U)) h0 n).trans
      (Category.comp_id _)


/-- The comparison of standard resolutions is compatible with the two augmentations, in every
simplicial degree. -/
theorem resolutionSectionsComparison_augmentation' (U : Cᵒᵖ) (i : SimplexCategoryᵒᵖ) :
    (resolutionSectionsComparison J f U).app i ≫
        (sectionsAlgebraFunctor J U).map ((standardResolution J f).hom.app i) =
      (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U)).hom.app i := by
  obtain ⟨⟨n⟩⟩ := i
  exact resolutionSectionsComparison_augmentation J f U n

/-- On sections, the comparison of standard resolutions carries the augmentation of the standard
resolution of `A(U) → B(U)` to the augmentation of the standard resolution of `A ⟶ B`. -/
theorem resolutionAugmentation_resolutionSectionsComparison (U : Cᵒᵖ) (i : SimplexCategoryᵒᵖ)
    (x : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj i) :
    (resolutionAugmentation J f i).hom.app U
        (((resolutionSectionsComparison J f U).app i).hom x) =
      CommAlgCat.standardResolutionAugmentationHom.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U) i x :=
  ConcreteCategory.congr_hom (resolutionSectionsComparison_augmentation' J f U i) x

/-- Sections over `U` of a sheaf of `B`-modules, as a module over the sections `B(U)`. -/
noncomputable abbrev moduleSections (U : Cᵒᵖ) :
    targetModules J B ⥤ ModuleCat.{max u v w} (sectionsAlgebra J f U) :=
  SheafOfModules.evaluation _ U

/-- Taking sections over `U` is additive. -/
instance moduleSections_additive (U : Cᵒᵖ) : (moduleSections J f U).Additive := by
  let : (SheafOfModules.forget.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf B)).Additive :=
    SheafOfModules.instAdditivePresheafOfModulesObjFunctorOppositeRingCatIsSheafForget _
  let : (PresheafOfModules.evaluation.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf B).obj U).Additive :=
    PresheafOfModules.instAdditiveModuleCatCarrierObjOppositeRingCatEvaluation _ _
  exact inferInstanceAs ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ U).Additive)

/-- The sections functor over `U` sends a morphism `h` of sheaves of modules to its component
`h.val.app U`. -/
@[simp]
theorem moduleSections_map_apply (U : Cᵒᵖ) {M N : targetModules J B} (h : M ⟶ N)
    (z : (moduleSections J f U).obj M) :
    (moduleSections J f U).map h z = h.val.app U z :=
  rfl

/-- The universal `A`-derivation of the degree-`i` term of the simplicial sheaf of modules
`Ω_{P_•/A} ⊗_{P_•} B`. -/
noncomputable abbrev universalSheafDerivation (i : SimplexCategoryᵒᵖ) :
    resolutionDerivations J f i ((cotangentSimplicialModule J f).object.obj i) :=
  (cotangentSimplicialModule J f).derivationEquiv i _ (𝟙 _)

/-- The `A(U)`-derivation of the degree-`i` term of the standard resolution of `A(U) → B(U)`
obtained by composing the comparison of standard resolutions with the universal derivation of
`Ω_{P_i/A} ⊗_{P_i} B`, taken on sections over `U`. -/
noncomputable def sectionsDerivation (U : Cᵒᵖ) (i : SimplexCategoryᵒᵖ) :
    (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U)).left.obj i →+
      (moduleSections J f U).obj ((cotangentSimplicialModule J f).object.obj i) :=
  ((universalSheafDerivation J f i).d (X := U)).comp
    (((resolutionSectionsComparison J f U).app i).hom.toRingHom.toAddMonoidHom)

/-- `sectionsDerivation` sends `x` to the universal derivation of the image of `x` under the
comparison of standard resolutions. -/
@[simp]
theorem sectionsDerivation_apply (U : Cᵒᵖ) (i : SimplexCategoryᵒᵖ)
    (x : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj i) :
    sectionsDerivation J f U i x =
      (universalSheafDerivation J f i).d (((resolutionSectionsComparison J f U).app i).hom x) :=
  rfl

/-- The derivation obtained from the comparison satisfies the Leibniz rule over the augmentation
of the standard resolution of `A(U) → B(U)`. -/
theorem sectionsDerivation_mul (U : Cᵒᵖ) (i : SimplexCategoryᵒᵖ)
    (x y : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj i) :
    sectionsDerivation J f U i (x * y) =
      CommAlgCat.standardResolutionAugmentationHom.{max u v w, max u v w} (A.obj.obj U)
          (sectionsAlgebra J f U) i x • sectionsDerivation J f U i y +
        CommAlgCat.standardResolutionAugmentationHom.{max u v w, max u v w} (A.obj.obj U)
          (sectionsAlgebra J f U) i y • sectionsDerivation J f U i x := by
  have hd := (universalSheafDerivation J f i).d_mul (X := U)
    (((resolutionSectionsComparison J f U).app i).hom x)
    (((resolutionSectionsComparison J f U).app i).hom y)
  have hx := resolutionAugmentation_resolutionSectionsComparison J f U i x
  have hy := resolutionAugmentation_resolutionSectionsComparison J f U i y
  rw [sectionsDerivation_apply, sectionsDerivation_apply, sectionsDerivation_apply, map_mul]
  refine hd.trans ?_
  rw [← hx, ← hy]
  rfl

/-- The derivation obtained from the comparison vanishes on the image of the base ring. -/
theorem sectionsDerivation_algebraMap (U : Cᵒᵖ) (i : SimplexCategoryᵒᵖ) (a : A.obj.obj U) :
    sectionsDerivation J f U i
      (algebraMap (A.obj.obj U)
        ((CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
          (sectionsAlgebra J f U)).left.obj i) a) = 0 := by
  rw [sectionsDerivation_apply,
    ((resolutionSectionsComparison J f U).app i).hom.commutes a]
  exact (universalSheafDerivation J f i).d_app a

/-- The canonical map on the degree-`i` term: the base-changed differentials of the standard
resolution of `A(U) → B(U)` map to the sections over `U` of `Ω_{P_i/A} ⊗_{P_i} B`. -/
noncomputable def cotangentTermComparison (U : Cᵒᵖ) (i : SimplexCategoryᵒᵖ) :
    CommAlgCat.cotangentTerm.{max u v w, max u v w} (A.obj.obj U) (sectionsAlgebra J f U) i ⟶
      (moduleSections J f U).obj ((cotangentSimplicialModule J f).object.obj i) :=
  CommAlgCat.cotangentTermDesc.{max u v w, max u v w} (A.obj.obj U) (sectionsAlgebra J f U) i _
    (sectionsDerivation J f U i) (sectionsDerivation_mul J f U i)
    (sectionsDerivation_algebraMap J f U i)

/-- `cotangentTermComparison` sends the differential of `p` to the universal derivation of the
image of `p` under the comparison of standard resolutions. -/
@[simp]
theorem cotangentTermComparison_differential (U : Cᵒᵖ) (i : SimplexCategoryᵒᵖ)
    (p : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj i) :
    cotangentTermComparison J f U i
        (CommAlgCat.cotangentTermDifferential.{max u v w, max u v w} (A.obj.obj U)
          (sectionsAlgebra J f U) i p) =
      (universalSheafDerivation J f i).d (((resolutionSectionsComparison J f U).app i).hom p) :=
  CommAlgCat.cotangentTermDesc_differential.{max u v w, max u v w} _ _ i _ _ _ _ p

/-- The universal derivation is natural in the simplex variable: a simplex map of the base-changed
differentials carries the universal differential of a section to the universal differential of its
image in the standard resolution. -/
theorem universalSheafDerivation_naturality {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j) (U : Cᵒᵖ)
    (x : (resolutionTerm J f i).obj.obj U) :
    ((cotangentSimplicialModule J f).object.map g).val.app U
        ((universalSheafDerivation J f i).d x) =
      (universalSheafDerivation J f j).d
        (((standardResolution J f).left.map g).right.hom.app U x) := by
  have h1 := (cotangentSimplicialModule J f).simplex_naturality g
    ((cotangentSimplicialModule J f).object.obj j) (𝟙 _) U x
  rw [Category.comp_id] at h1
  have h2 := (cotangentSimplicialModule J f).naturality i (𝟙 _)
    ((cotangentSimplicialModule J f).object.map g)
  rw [Category.id_comp] at h2
  rw [← h1, h2]
  rfl

/-- The comparison of standard resolutions is natural in the simplex variable, on sections: a
simplex map carries the image of a section to the image of its image. -/
theorem resolutionSectionsComparison_naturality_apply (U : Cᵒᵖ) {i j : SimplexCategoryᵒᵖ}
    (g : i ⟶ j)
    (p : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj i) :
    ((resolutionSectionsComparison J f U).app j).hom
        ((CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
          (sectionsAlgebra J f U)).left.map g p) =
      ((standardResolution J f).left.map g).right.hom.app U
        (((resolutionSectionsComparison J f U).app i).hom p) :=
  ConcreteCategory.congr_hom ((resolutionSectionsComparison J f U).naturality g) p

/-- The degreewise comparison of base-changed differentials commutes with every simplicial
operator, evaluated at a pure differential `1 ⊗ d p`. -/
theorem cotangentTermComparison_naturality_apply (U : Cᵒᵖ) {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j)
    (p : (CommAlgCat.standardResolution.{max u v w, max u v w} (A.obj.obj U)
      (sectionsAlgebra J f U)).left.obj i) :
    cotangentTermComparison J f U j
        ((CommAlgCat.cotangentSimplicialModule.{max u v w, max u v w} (A.obj.obj U)
            (sectionsAlgebra J f U)).object.map g
          (CommAlgCat.cotangentTermDifferential.{max u v w, max u v w} (A.obj.obj U)
            (sectionsAlgebra J f U) i p)) =
      ((cotangentSimplicialModule J f).object.map g).val.app U
        (cotangentTermComparison J f U i
          (CommAlgCat.cotangentTermDifferential.{max u v w, max u v w} (A.obj.obj U)
            (sectionsAlgebra J f U) i p)) := by
  rw [CommAlgCat.cotangentSimplicialModule_map_differential, cotangentTermComparison_differential,
    cotangentTermComparison_differential, resolutionSectionsComparison_naturality_apply]
  exact (universalSheafDerivation_naturality J f g U _).symm

/-- The base-changed differentials of the standard resolution of `A(U) → B(U)` map canonically to
the sections over `U` of the base-changed differentials of the standard resolution of `A ⟶ B`, as
simplicial `B(U)`-modules. -/
noncomputable def cotangentSimplicialComparison (U : Cᵒᵖ) :
    (CommAlgCat.cotangentSimplicialModule.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U)).object ⟶
      (cotangentSimplicialModule J f).object ⋙ moduleSections J f U where
  app i := cotangentTermComparison J f U i
  naturality _ _ g :=
    CommAlgCat.cotangentTerm_hom_ext.{max u v w, max u v w} _ _ _ _ _
      (cotangentTermComparison_naturality_apply J f U g)

/-- The degree-`i` component of `cotangentSimplicialComparison` is `cotangentTermComparison`
in degree `i`. -/
@[simp]
theorem cotangentSimplicialComparison_app (U : Cᵒᵖ) (i : SimplexCategoryᵒᵖ) :
    (cotangentSimplicialComparison J f U).app i = cotangentTermComparison J f U i :=
  rfl

/-- The induced map of alternating-face-map (Moore) complexes of `B(U)`-modules. -/
noncomputable def cotangentMooreComparison (U : Cᵒᵖ) :
    (AlgebraicTopology.alternatingFaceMapComplex
          (ModuleCat.{max u v w} (sectionsAlgebra J f U))).obj
        (CommAlgCat.cotangentSimplicialModule.{max u v w, max u v w} (A.obj.obj U)
          (sectionsAlgebra J f U)).object ⟶
      ((moduleSections J f U).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((AlgebraicTopology.alternatingFaceMapComplex (targetModules J B)).obj
          (cotangentSimplicialModule J f).object) :=
  (AlgebraicTopology.alternatingFaceMapComplex
        (ModuleCat.{max u v w} (sectionsAlgebra J f U))).map
      (cotangentSimplicialComparison J f U) ≫
    ((AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
        (moduleSections J f U)).app (cotangentSimplicialModule J f).object).inv

/-- In simplicial degree `n` the map of Moore complexes is the degreewise comparison. -/
@[simp]
theorem cotangentMooreComparison_f (U : Cᵒᵖ) (n : ℕ) :
    (cotangentMooreComparison J f U).f n = cotangentTermComparison J f U (op ⦋n⦌) :=
  Category.comp_id _

/-- The canonical map `L_{B(U)/A(U)} ⟶ L_{B/A}(U)` of complexes of `B(U)`-modules: the comparison
of standard resolutions, base-changed on differentials, pushed through the alternating-face-map
complex and through the reindexing which places simplicial degree `n` in cohomological degree
`-n`. -/
@[stacks 08SX "the canonical map L_{B(U)/A(U)} ⟶ L_{B/A}(U); not the sheafification clause"]
noncomputable def sectionsCotangentComplexComparison (U : Cᵒᵖ) :
    CommAlgCat.cotangentComplex.{max u v w, max u v w} (A.obj.obj U)
        (sectionsAlgebra J f U) ⟶
      ((moduleSections J f U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (cotangentComplex J f) :=
  HomologicalComplex.extendMap (cotangentMooreComparison J f U)
      (ComplexShape.embeddingUpIntLE 0) ≫
    (HomologicalComplex.mapHomologicalComplexExtendIso (moduleSections J f U)
      ((AlgebraicTopology.alternatingFaceMapComplex (targetModules J B)).obj
        (cotangentSimplicialModule J f).object)
      (ComplexShape.embeddingUpIntLE 0)).hom

/-- In cohomological degree `-n` the canonical map is the degreewise comparison of base-changed
differentials, read through the two canonical degree isomorphisms. -/
theorem sectionsCotangentComplexComparison_f (U : Cᵒᵖ) (n : ℕ) :
    (sectionsCotangentComplexComparison J f U).f (-(n : ℤ)) =
      (CommAlgCat.cotangentComplex_degreeIso.{max u v w, max u v w} (A.obj.obj U)
          (sectionsAlgebra J f U) n).hom ≫
        cotangentTermComparison J f U (op ⦋n⦌) ≫
          (moduleSections J f U).map (cotangentComplex_degreeIso J f n).inv := by
  have h : (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = -(n : ℤ) := by simp
  refine (HomologicalComplex.extendMap_mapHomologicalComplexExtendIso_f _ _
    (cotangentMooreComparison J f U) (ComplexShape.embeddingUpIntLE 0) h).trans ?_
  rw [cotangentMooreComparison_f]
  rfl

end CategoryTheory.Sheaf

end
