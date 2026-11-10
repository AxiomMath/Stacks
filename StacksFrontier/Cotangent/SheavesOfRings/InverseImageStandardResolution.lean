module

public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoiRing
public import StacksFrontier.Cotangent.SheavesOfRings.CotangentComplex

/-!
# The inverse image of the free algebra sheaf and of the standard resolution

Let `f : Sh(C) ⟶ Sh(D)` be a morphism of topoi and `A` a sheaf of commutative rings on `D`.
Inverse image of sheaves of `A`-algebras commutes with the free–forgetful adjunction: the
forgetful square commutes on the nose and the free square commutes by the canonical comparison
of left adjoints, compatibly with the units. Consequently the two free–forgetful comonads, whose
iterates are the terms of the standard resolution, are compared by a canonical isomorphism.

## Main definitions

* `CategoryTheory.Adjunction.comonadSquareIso` compares the two comonads attached to a commuting
  square of adjunctions.
* `CategoryTheory.Functor.iterateCompIso` iterates a comparison of commuting endofunctors.
* `CategoryTheory.SimplicialObject.isoOfFacesAndDegeneracies` builds an isomorphism of simplicial
  objects from degreewise isomorphisms commuting with the faces and the degeneracies.
* `CategoryTheory.Sheaf.standardResolutionIterate` and
  `CategoryTheory.Sheaf.standardResolutionGenerator` present the degree-`n` term of the standard
  resolution as a free algebra sheaf together with its generators.
* `CategoryTheory.Sheaf.freeAlgebraSheafInverseImageIso` identifies the inverse image of the free
  `A`-algebra sheaf on a sheaf of sets with the free `f⁻¹A`-algebra sheaf on its inverse image.
* `CategoryTheory.Sheaf.standardResolutionComonadInverseImageIso` is the induced comparison of
  the two free–forgetful comonads.

## Main results

* `CategoryTheory.MorphismOfTopoi.ringAdjunction_unit_forget`: the unit of the adjunction
  `f⁻¹ ⊣ f_*` on sheaves of commutative rings is the unit on underlying sheaves of sets.
* `CategoryTheory.Sheaf.forgetAlgebraSheafInverseImageIso`: the inverse image of a sheaf of
  `A`-algebras has the inverse image of the underlying sheaf of sets.
* `CategoryTheory.Sheaf.freeAlgebraSheafInverseImageIso_unit`: the comparison of the free algebra
  functors carries the unit of the free–forgetful adjunction on the target to the unit on the
  source. Together with `forgetAlgebraSheafInverseImageIso` this is the commuting square of
  adjunctions on which the inverse image of the standard resolution rests.
* `CategoryTheory.Sheaf.standardResolution_delta`,
  `CategoryTheory.Sheaf.standardResolution_sigma` and
  `CategoryTheory.Sheaf.standardResolution_augmentation_app_zero`: the faces, degeneracies and
  augmentation of the standard resolution are Godement's, read through the identification of its
  terms with the iterates of the free–forgetful comonad.

## Implementation notes

The forgetful square commutes on the nose on objects, the inverse image of sheaves of
commutative rings being the geometric inverse image of the underlying sheaf of sets with the
operations carried along, and the inverse image of algebras being `Under.post` of it; on
morphisms the comparison is `MorphismOfTopoi.inverseImageRing_map_forget`, so the isomorphism is
built from reflexivity components rather than being a reflexivity isomorphism of functors.

The free square is the uniqueness of a left adjoint. The relevant right adjoint has to be
produced at the spelling `forgetAlgebraSheaf J (f⁻¹A) ⋙ f_*`, whereas composing the
free–forgetful adjunction with `Under.postAdjunctionLeft` produces it at the spelling
`(Under.post f_* ⋙ Under.map unit) ⋙ forgetAlgebraSheaf K A`; the two agree on objects and are
compared on morphisms by `MorphismOfTopoi.pushforwardRing_map_forget`, so the adjunction is
transported along that isomorphism with `Adjunction.ofNatIsoRight`.

The abstract lemmas about a commuting square of adjunctions are stated for arbitrary categories
and are proved here once; instantiating them at the sheaf categories involved is expensive
enough that `freeAlgebraSheafInverseImageIso_unit` repeats the argument of
`Adjunction.map_unit_comp_leftAdjointUniq_hom_app` directly on the concrete functors instead of
invoking it.

### Tag 08SV

Tag 08SV, `f⁻¹L_{B/A} = L_{f⁻¹B/f⁻¹A}`, rests on the square of adjunctions constructed here: the
induced comparison of standard resolutions is
`CategoryTheory.Sheaf.standardResolutionInverseImageIso` and the statement itself is
`CategoryTheory.Sheaf.inverseImageCotangentComplexIso`.

The two sites, their morphism universes and the two universes of sections all vary
independently, as in `CategoryTheory.Sheaf.cotangentComplex`.

## References

* [Stacks Project, Tag 08SV](https://stacks.math.columbia.edu/tag/08SV)
* [Stacks Project, Tag 08SR](https://stacks.math.columbia.edu/tag/08SR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial


namespace CategoryTheory

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

section AdjointSquare

variable {S : Type u₁} [Category.{v₁} S] {T : Type u₂} [Category.{v₂} T]
  {A : Type u₃} [Category.{v₃} A] {B : Type u₄} [Category.{v₄} B]
  {F : S ⥤ A} {U : A ⥤ S} {F' : T ⥤ B} {U' : B ⥤ T} {L : S ⥤ T} {R : T ⥤ S} {H : A ⥤ B}

/-- In a commuting square of adjunctions, the comparison of the left adjoints obtained from the
uniqueness of a left adjoint carries the unit of the top adjunction to the unit of the bottom
one. -/
lemma Adjunction.map_unit_comp_leftAdjointUniq_hom_app (a : F ⊣ U) (b : F' ⊣ U')
    (l : L ⊣ R) (c : F ⋙ H ⊣ U' ⋙ R) (i : H ⋙ U' ≅ U ⋙ L)
    (hc : ∀ X, c.unit.app X = a.unit.app X ≫
      l.unit.app (U.obj (F.obj X)) ≫ R.map (i.inv.app (F.obj X))) (X : S) :
    L.map (a.unit.app X) ≫ i.inv.app (F.obj X) ≫
        U'.map ((Adjunction.leftAdjointUniq c (l.comp b)).hom.app X) =
      b.unit.app (L.obj X) := by
  apply (l.homEquiv _ _).injective
  have he := Adjunction.unit_leftAdjointUniq_hom_app c (l.comp b) X
  rw [hc, Adjunction.comp_unit_app] at he
  simp only [Adjunction.homEquiv_apply, Functor.map_comp]
  rw [← Category.assoc, ← Category.assoc, l.unit_naturality]
  simpa only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Category.assoc] using he

/-- The comparison of the comonads `U ⋙ F` and `U' ⋙ F'` attached to a commuting square of
adjunctions, assembled from the comparisons of the left and of the right adjoints. -/
def Adjunction.comonadSquareIso (e : F ⋙ H ≅ L ⋙ F') (i : H ⋙ U' ≅ U ⋙ L) :
    (U ⋙ F) ⋙ H ≅ H ⋙ (U' ⋙ F') :=
  Functor.isoWhiskerLeft U e ≪≫ Functor.isoWhiskerRight i.symm F'

/-- The components of the comonad comparison, unfolded. -/
private lemma Adjunction.comonadSquareIso_hom_app (e : F ⋙ H ≅ L ⋙ F') (i : H ⋙ U' ≅ U ⋙ L)
    (X : A) : (Adjunction.comonadSquareIso e i).hom.app X =
      e.hom.app (U.obj X) ≫ F'.map (i.inv.app X) := by
  simp [Adjunction.comonadSquareIso]

/-- The comonad comparison commutes with the counits of the two adjunctions. -/
lemma Adjunction.comonadSquareIso_counit (a : F ⊣ U) (b : F' ⊣ U')
    (e : F ⋙ H ≅ L ⋙ F') (i : H ⋙ U' ≅ U ⋙ L)
    (he : ∀ X, L.map (a.unit.app X) ≫ i.inv.app (F.obj X) ≫
      U'.map (e.hom.app X) = b.unit.app (L.obj X)) (X : A) :
    (Adjunction.comonadSquareIso e i).hom.app X ≫ b.counit.app (H.obj X) =
      H.map (a.counit.app X) := by
  apply (cancel_epi (e.inv.app (U.obj X))).1
  simp only [Adjunction.comonadSquareIso_hom_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  apply (b.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_apply, Functor.map_comp]
  calc
    _ = i.inv.app X := by
      have hn := b.unit_naturality (i.inv.app X)
      dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hn
      rw [← Category.assoc, hn]
      simp only [Category.assoc, b.right_triangle_components, Category.comp_id]
    _ = _ := by
      rw [← he]
      simp only [Category.assoc, ← U'.map_comp, Iso.hom_inv_id_app_assoc]
      have hn := i.inv.naturality (a.counit.app X)
      dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
      rw [← hn, ← Category.assoc, ← L.map_comp, a.right_triangle_components]
      change i.inv.app X = L.map (𝟙 (U.obj X)) ≫ i.inv.app X
      rw [L.map_id (U.obj X), Category.id_comp]

/-- The comonad comparison commutes with the comultiplications of the two comonads. -/
lemma Adjunction.comonadSquareIso_comul (a : F ⊣ U) (b : F' ⊣ U')
    (e : F ⋙ H ≅ L ⋙ F') (i : H ⋙ U' ≅ U ⋙ L)
    (he : ∀ X, L.map (a.unit.app X) ≫ i.inv.app (F.obj X) ≫
      U'.map (e.hom.app X) = b.unit.app (L.obj X)) (X : A) :
    H.map (F.map (a.unit.app (U.obj X))) ≫
        (Adjunction.comonadSquareIso e i).hom.app (F.obj (U.obj X)) ≫
        F'.map (U'.map ((Adjunction.comonadSquareIso e i).hom.app X)) =
      (Adjunction.comonadSquareIso e i).hom.app X ≫
        F'.map (b.unit.app (U'.obj (H.obj X))) := by
  have hn := e.hom.naturality (a.unit.app (U.obj X))
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  simp only [Adjunction.comonadSquareIso_hom_app, Category.assoc]
  rw [← Category.assoc, hn, Category.assoc]
  simp only [← F'.map_comp, U'.map_comp]
  have hu := b.unit_naturality (i.inv.app X)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hu
  apply congrArg (fun z => e.hom.app (U.obj X) ≫ F'.map z)
  rw [← Category.assoc, ← Category.assoc, Category.assoc (L.map _) (i.inv.app _) (U'.map _), he, hu]

/-- Transposing a morphism out of the image of the comonad comparison through the bottom
adjunction factors the unit of the top adjunction through the comparison of the right
adjoints. -/
lemma Adjunction.comonadSquareIso_unit (a : F ⊣ U) (b : F' ⊣ U')
    (e : F ⋙ H ≅ L ⋙ F') (i : H ⋙ U' ≅ U ⋙ L)
    (he : ∀ X, L.map (a.unit.app X) ≫ i.inv.app (F.obj X) ≫
      U'.map (e.hom.app X) = b.unit.app (L.obj X))
    (X : A) (Y : B) (k : H.obj X ⟶ Y) :
    i.inv.app X ≫ U'.map k ≫ b.unit.app (U'.obj Y) =
      L.map (a.unit.app (U.obj X)) ≫ i.inv.app (F.obj (U.obj X)) ≫
        U'.map ((Adjunction.comonadSquareIso e i).hom.app X ≫ F'.map (U'.map k)) := by
  have hn := b.unit_naturality (i.inv.app X ≫ U'.map k)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  simp only [Adjunction.comonadSquareIso_hom_app, Functor.map_comp, Category.assoc]
  calc
    _ = b.unit.app (L.obj (U.obj X)) ≫ U'.map (F'.map (i.inv.app X)) ≫
        U'.map (F'.map (U'.map k)) := by
      simpa only [Functor.map_comp, Category.assoc] using hn.symm
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ U'.map (F'.map (i.inv.app X)) ≫ U'.map (F'.map (U'.map k)))
        (he (U.obj X)).symm

end AdjointSquare

section Iterate

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A comparison `G ⋙ H ≅ H ⋙ G'` of commuting endofunctors, iterated `n` times. -/
def Functor.iterateCompIso {G : C ⥤ C} {G' : D ⥤ D} {H : C ⥤ D}
    (e : G ⋙ H ≅ H ⋙ G') : (n : ℕ) → G.iterate n ⋙ H ≅ H ⋙ G'.iterate n
  | 0 => Iso.refl H
  | n + 1 => Functor.isoWhiskerLeft (G.iterate n) e ≪≫
      Functor.isoWhiskerRight (Functor.iterateCompIso e n) G'

/-- At the first iterate the comparison still commutes with the given counits. -/
lemma Functor.iterateCompIso_one_counit {G : C ⥤ C} {G' : D ⥤ D} {H : C ⥤ D}
    (e : G ⋙ H ≅ H ⋙ G') (ε : G ⟶ 𝟭 C) (ε' : G' ⟶ 𝟭 D)
    (hε : ∀ X, e.hom.app X ≫ ε'.app (H.obj X) = H.map (ε.app X)) (X : C) :
    (Functor.iterateCompIso e 1).hom.app X ≫ ε'.app (H.obj X) = H.map (ε.app X) := by
  simpa [Functor.iterateCompIso, Functor.iterate] using hε X

/-- The iterated comparison commutes with Godement's face maps. -/
lemma Functor.iterateCompIso_godementFace {G : C ⥤ C} {G' : D ⥤ D} {H : C ⥤ D}
    (e : G ⋙ H ≅ H ⋙ G') (ε : G ⟶ 𝟭 C) (ε' : G' ⟶ 𝟭 D)
    (hε : ∀ X, e.hom.app X ≫ ε'.app (H.obj X) = H.map (ε.app X))
    (n : ℕ) (j : Fin (n + 1)) (X : C) :
    H.map ((Godement.face ε n j).app X) ≫ (Functor.iterateCompIso e n).hom.app X =
      (Functor.iterateCompIso e (n + 1)).hom.app X ≫ (Godement.face ε' n j).app (H.obj X) := by
  induction n with
  | zero =>
    simpa [Godement.face, Functor.iterateCompIso, Functor.iterate] using (hε X).symm
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Godement.Prep.face_zero, whiskerLeft_app]
      change H.map (ε.app ((G.iterate (n + 1)).obj X)) ≫ _ =
        (e.hom.app _ ≫ G'.map ((Functor.iterateCompIso e (n + 1)).hom.app X)) ≫ _
      have hn := ε'.naturality ((Functor.iterateCompIso e (n + 1)).hom.app X)
      dsimp only [Functor.id_map, Functor.comp_obj] at hn
      rw [Category.assoc, hn, ← Category.assoc, hε]
    · simp only [Godement.Prep.face_succ, whiskerRight_app]
      change H.map (G.map ((Godement.face ε n j).app X)) ≫
        (e.hom.app _ ≫ G'.map ((Functor.iterateCompIso e n).hom.app X)) =
        (e.hom.app _ ≫ G'.map ((Functor.iterateCompIso e (n + 1)).hom.app X)) ≫
          G'.map ((Godement.face ε' n j).app (H.obj X))
      have hn := e.hom.naturality ((Godement.face ε n j).app X)
      dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
      rw [← Category.assoc, hn]
      simp only [Category.assoc, ← G'.map_comp, ih j]

/-- The iterated comparison commutes with Godement's degeneracy maps. -/
lemma Functor.iterateCompIso_godementDegeneracy {G : C ⥤ C} {G' : D ⥤ D} {H : C ⥤ D}
    (e : G ⋙ H ≅ H ⋙ G') (δ : G ⟶ G ⋙ G) (δ' : G' ⟶ G' ⋙ G')
    (hδ : ∀ X, H.map (δ.app X) ≫ e.hom.app (G.obj X) ≫ G'.map (e.hom.app X) =
      e.hom.app X ≫ δ'.app (H.obj X))
    (n : ℕ) (j : Fin (n + 1)) (X : C) :
    H.map ((Godement.degeneracy δ n j).app X) ≫
        (Functor.iterateCompIso e (n + 2)).hom.app X =
      (Functor.iterateCompIso e (n + 1)).hom.app X ≫
        (Godement.degeneracy δ' n j).app (H.obj X) := by
  induction n with
  | zero =>
    simpa [Godement.degeneracy, Functor.iterateCompIso, Functor.iterate] using hδ X
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Godement.Prep.degeneracy_zero, whiskerLeft_app]
      change H.map (δ.app ((G.iterate (n + 1)).obj X)) ≫
        (e.hom.app _ ≫ G'.map (e.hom.app _ ≫
          G'.map ((Functor.iterateCompIso e (n + 1)).hom.app X))) =
        (e.hom.app _ ≫ G'.map ((Functor.iterateCompIso e (n + 1)).hom.app X)) ≫ _
      have hn := δ'.naturality ((Functor.iterateCompIso e (n + 1)).hom.app X)
      dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
      rw [Category.assoc, hn]
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun k => k ≫ G'.map (G'.map
          ((Functor.iterateCompIso e (n + 1)).hom.app X)))
          (hδ ((G.iterate (n + 1)).obj X))
    · simp only [Godement.Prep.degeneracy_succ, whiskerRight_app]
      change H.map (G.map ((Godement.degeneracy δ n j).app X)) ≫
        (e.hom.app _ ≫ G'.map ((Functor.iterateCompIso e (n + 2)).hom.app X)) =
        (e.hom.app _ ≫ G'.map ((Functor.iterateCompIso e (n + 1)).hom.app X)) ≫
          G'.map ((Godement.degeneracy δ' n j).app (H.obj X))
      have hn := e.hom.naturality ((Godement.degeneracy δ n j).app X)
      dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
      rw [← Category.assoc, hn]
      simp only [Category.assoc, ← G'.map_comp, ih j]

end Iterate

section Simplicial

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Degreewise isomorphisms commuting with every face and every degeneracy map assemble into an
isomorphism of simplicial objects, the faces and degeneracies generating every simplex map. -/
def SimplicialObject.isoOfFacesAndDegeneracies {X Y : SimplicialObject C}
    (e : ∀ n, X.obj (op ⦋n⦌) ≅ Y.obj (op ⦋n⦌))
    (hδ : ∀ n (j : Fin (n + 2)), X.δ j ≫ (e n).hom = (e (n + 1)).hom ≫ Y.δ j)
    (hσ : ∀ n (j : Fin (n + 1)), X.σ j ≫ (e (n + 1)).hom = (e n).hom ≫ Y.σ j) :
    X ≅ Y := by
  let W : MorphismProperty SimplexCategory := fun {a b} g =>
    X.map g.op ≫ (e a.len).hom = (e b.len).hom ≫ Y.map g.op
  have : W.IsMultiplicative :=
    { id_mem := fun a => by simp [W]
      comp_mem := fun g h hg hh => by
        dsimp only [W] at *
        simp only [op_comp, Functor.map_comp, Category.assoc]
        rw [hg, ← Category.assoc, hh, Category.assoc] }
  have hw : W = ⊤ := SimplexCategory.morphismProperty_eq_top W (fun j => hδ _ j) (fun j => hσ _ j)
  exact NatIso.ofComponents (fun n => e n.unop.len) fun g => show W g.unop by rw [hw]; trivial

/-- A morphism to a constant simplicial object, pushed along a functor. -/
def SimplicialObject.mapToConst (H : C ⥤ D) {X : SimplicialObject C} {B : C}
    (a : X ⟶ (SimplicialObject.const C).obj B) :
    X ⋙ H ⟶ (SimplicialObject.const D).obj (H.obj B) where
  app n := H.map (a.app n)
  naturality i j g := by
    have h := a.naturality g
    dsimp only [Functor.comp_map, Functor.comp_obj, SimplicialObject.const] at h ⊢
    rw [← H.map_comp, h, H.map_comp]
    simp

/-- An isomorphism of simplicial objects compatible in degree zero with two morphisms to constant
objects is compatible with them in every degree. -/
lemma SimplicialObject.hom_comp_toConst_of_zero {X Y : SimplicialObject C} {B B' : C}
    (a : X ⟶ (SimplicialObject.const C).obj B)
    (b : Y ⟶ (SimplicialObject.const C).obj B') (e : X ≅ Y) (c : B ⟶ B')
    (h₀ : (e.hom.app (op ⦋0⦌)) ≫ b.app (op ⦋0⦌) = a.app (op ⦋0⦌) ≫ c)
    (n : ℕ) : e.hom.app (op ⦋n⦌) ≫ b.app (op ⦋n⦌) = a.app (op ⦋n⦌) ≫ c := by
  induction n with
  | zero => exact h₀
  | succ n ih =>
    have key : ∀ {Z : SimplicialObject C} {B : C} (z : Z ⟶ (SimplicialObject.const C).obj B),
        Z.map (SimplexCategory.δ (0 : Fin (n + 2))).op ≫ z.app (op ⦋n⦌) = z.app (op ⦋n + 1⦌) :=
      fun z => (z.naturality (SimplexCategory.δ (0 : Fin (n + 2))).op).trans (Category.comp_id _)
    rw [← key b, ← Category.assoc, ← e.hom.naturality, Category.assoc, ih, ← Category.assoc, key a]

end Simplicial

section Transport

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- An isomorphism between the value of a functor and an object, transported along equalities of
the source and of the target. -/
def Functor.transportObjIso (H : C ⥤ D) {X X' : C} {Y Y' : D}
    (p : X = X') (q : Y = Y') (e : H.obj X' ≅ Y') : H.obj X ≅ Y :=
  H.mapIso (eqToIso p) ≪≫ e ≪≫ eqToIso q.symm

/-- Transported isomorphisms are natural for morphisms which are the transports of a naturality
square for the untransported ones. -/
lemma Functor.transportObjIso_naturality (H : C ⥤ D)
    {X₁ X₁' X₂ X₂' : C} {Y₁ Y₁' Y₂ Y₂' : D}
    (p₁ : X₁ = X₁') (p₂ : X₂ = X₂') (q₁ : Y₁ = Y₁') (q₂ : Y₂ = Y₂')
    (e₁ : H.obj X₁' ≅ Y₁') (e₂ : H.obj X₂' ≅ Y₂')
    {a : X₁ ⟶ X₂} {a' : X₁' ⟶ X₂'} {b : Y₁ ⟶ Y₂} {b' : Y₁' ⟶ Y₂'}
    (ha : a = eqToHom p₁ ≫ a' ≫ eqToHom p₂.symm)
    (hb : b = eqToHom q₁ ≫ b' ≫ eqToHom q₂.symm)
    (h : H.map a' ≫ e₂.hom = e₁.hom ≫ b') :
    H.map a ≫ (Functor.transportObjIso H p₂ q₂ e₂).hom =
      (Functor.transportObjIso H p₁ q₁ e₁).hom ≫ b := by
  subst p₁ p₂ q₁ q₂
  simpa [Functor.transportObjIso, ha, hb] using h

end Transport

section RingUnit

universe w w'

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))

/-- The underlying morphism of sheaves of sets of the unit of the adjunction `f⁻¹ ⊣ f_*` on
sheaves of commutative rings is the unit of `f⁻¹ ⊣ f_*` on sheaves of sets. -/
lemma MorphismOfTopoi.ringAdjunction_unit_forget (O : Sheaf K CommRingCat.{w'}) :
    (sheafCompose K (forget CommRingCat.{w'})).map (f.ringAdjunction.unit.app O) =
      f.adj.unit.app ((sheafCompose K (forget CommRingCat.{w'})).obj O) :=
  (congrArg (sheafCompose K (forget CommRingCat.{w'})).map
      (f.ringAdjunction.homEquiv_id O).symm).trans
    ((f.ringAdjunction_homEquiv_forget O _ (𝟙 _)).trans
      ((congrArg (f.adj.homEquiv _ _)
        ((sheafCompose J (forget CommRingCat.{w})).map_id _)).trans (f.adj.homEquiv_id _)))

end RingUnit

end CategoryTheory

namespace CategoryTheory.Sheaf

universe u v w u' v' w'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

section Resolution

variable (J : GrothendieckTopology C) {A B : Sheaf J CommRingCat.{max u v w}}

/-- The sheaf of `A`-algebras which freely generates the degree-`n` term of the standard
resolution: the `n`-fold iterate of the free–forgetful comonad applied to `B`. -/
noncomputable abbrev standardResolutionIterate (a : A ⟶ B) (n : ℕ) : Under A :=
  (((standardResolutionComonad J A : Comonad (Under A)) : Under A ⥤ Under A).iterate n).obj
    (Under.mk a)

/-- The degree-`n` term of the standard resolution is the free `A`-algebra sheaf on the
underlying sheaf of sets of the `n`-fold iterate. -/
theorem standardResolution_obj_eq_free (a : A ⟶ B) (n : ℕ) :
    (standardResolution.{v, u, w} J a).left.obj (op ⦋n⦌) =
      (freeAlgebraSheaf.{v, u, w} J A).obj
        ((forgetAlgebraSheaf.{v, u, w} J A).obj (standardResolutionIterate J a n)) := by
  rw [standardResolution_obj.{v, u, w}]
  rfl

/-- The free generators of the degree-`n` term of the standard resolution: the unit of the
free–forgetful adjunction at the underlying sheaf of sets of the `n`-fold iterate. -/
noncomputable def standardResolutionGenerator (a : A ⟶ B) (n : ℕ) :
    (forgetAlgebraSheaf.{v, u, w} J A).obj (standardResolutionIterate J a n) ⟶
      (forgetAlgebraSheaf.{v, u, w} J A).obj
        ((standardResolution.{v, u, w} J a).left.obj (op ⦋n⦌)) :=
  (freeAlgebraSheafAdjunction.{v, u, w} J A).unit.app _ ≫
    (forgetAlgebraSheaf.{v, u, w} J A).map
      (eqToHom (standardResolution_obj_eq_free J a n).symm)

/-- The face maps of the standard resolution are Godement's, read through the identification of
its terms with the iterates of the free–forgetful comonad. -/
theorem standardResolution_delta (a : A ⟶ B) (n : ℕ) (j : Fin (n + 2)) :
    (standardResolution.{v, u, w} J a).left.δ j =
      eqToHom (standardResolution_obj.{v, u, w} J a (n + 1)) ≫
        (Godement.face (standardResolutionComonad.{v, u, w} J A).ε (n + 1) j).app (Under.mk a) ≫
        eqToHom (standardResolution_obj.{v, u, w} J a n).symm := by
  change ((standardResolutionFunctor.{v, u, w} J A).left.δ j).app (Under.mk a) = _
  rw [standardResolutionFunctor_face.{v, u, w}]
  simp only [NatTrans.comp_app, eqToHom_app]
  rfl

/-- The degeneracy maps of the standard resolution are Godement's, read through the same
identification. -/
theorem standardResolution_sigma (a : A ⟶ B) (n : ℕ) (j : Fin (n + 1)) :
    (standardResolution.{v, u, w} J a).left.σ j =
      eqToHom (standardResolution_obj.{v, u, w} J a n) ≫
        (Godement.degeneracy (standardResolutionComonad.{v, u, w} J A).δ n j).app (Under.mk a) ≫
        eqToHom (standardResolution_obj.{v, u, w} J a (n + 1)).symm := by
  change ((standardResolutionFunctor.{v, u, w} J A).left.σ j).app (Under.mk a) = _
  rw [standardResolutionFunctor_degeneracy.{v, u, w}]
  simp only [NatTrans.comp_app, eqToHom_app]
  rfl

/-- In degree zero the augmentation of the standard resolution is the counit of the
free–forgetful comonad. -/
theorem standardResolution_augmentation_app_zero (a : A ⟶ B) :
    (standardResolution.{v, u, w} J a).hom.app (op ⦋0⦌) =
      eqToHom (standardResolution_obj.{v, u, w} J a 0) ≫
        (standardResolutionComonad.{v, u, w} J A).ε.app (Under.mk a) := by
  change ((standardResolutionFunctor.{v, u, w} J A).hom.app (op ⦋0⦌)).app (Under.mk a) ≫
    eqToHom (Functor.congr_obj
      (standardResolutionFunctor_point.{v, u, w} J A) (Under.mk a)) = _
  rw [standardResolutionFunctor_augmentation.{v, u, w}]
  simp only [NatTrans.comp_app, eqToHom_app, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id]
  rfl

end Resolution

section FreeAlgebraComparison

variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (f : MorphismOfTopoi (Sheaf J (Type (max u v w))) (Sheaf K (Type (max u' v' w'))))
  (A : Sheaf K CommRingCat.{max u' v' w'})

/-- The square of forgetful functors and inverse images commutes: the inverse image of a sheaf of
`A`-algebras has the inverse image of the underlying sheaf of sets. -/
@[implicit_reducible]
noncomputable def forgetAlgebraSheafInverseImageIso :
    Under.post (X := A) f.inverseImageRing ⋙
        forgetAlgebraSheaf.{v, u, w} J (f.inverseImageRing.obj A) ≅
      forgetAlgebraSheaf.{v', u', w'} K A ⋙ f.inverseImage :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {_ _} g =>
    (Category.comp_id _).trans
      ((f.inverseImageRing_map_forget g.right).trans (Category.id_comp _).symm))

/-- The same square for the direct images, in the spelling produced by composing the
free–forgetful adjunction with `Under.postAdjunctionLeft`. -/
@[implicit_reducible]
noncomputable def forgetAlgebraSheafPushforwardIso :
    (Under.post (X := f.inverseImageRing.obj A) f.pushforwardRing ⋙
          Under.map (f.ringAdjunction.unit.app A)) ⋙
        forgetAlgebraSheaf.{v', u', w'} K A ≅
      forgetAlgebraSheaf.{v, u, w} J (f.inverseImageRing.obj A) ⋙ f.pushforward :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {_ _} g =>
    (Category.comp_id _).trans
      ((f.pushforwardRing_map_forget g.right).trans (Category.id_comp _).symm))

/-- The free–forgetful adjunction of `A`-algebras on the target, composed with the inverse image
of algebras and with the inverse image of sheaves of sets. -/
@[implicit_reducible]
noncomputable def freeAlgebraSheafInverseImageAdjunction :
    freeAlgebraSheaf.{v', u', w'} K A ⋙ Under.post (X := A) f.inverseImageRing ⊣
      forgetAlgebraSheaf.{v, u, w} J (f.inverseImageRing.obj A) ⋙ f.pushforward :=
  ((freeAlgebraSheafAdjunction.{v', u', w'} K A).comp
    (Under.postAdjunctionLeft (X := A) f.ringAdjunction)).ofNatIsoRight
      (forgetAlgebraSheafPushforwardIso J K f A)

/-- The unit of that composite adjunction is the unit of the free–forgetful adjunction followed
by the unit of `f⁻¹ ⊣ f_*`. -/
lemma freeAlgebraSheafInverseImageAdjunction_unit (X : Sheaf K (Type (max u' v' w'))) :
    (freeAlgebraSheafInverseImageAdjunction J K f A).unit.app X =
      (freeAlgebraSheafAdjunction.{v', u', w'} K A).unit.app X ≫
        f.adj.unit.app ((forgetAlgebraSheaf.{v', u', w'} K A).obj
          ((freeAlgebraSheaf.{v', u', w'} K A).obj X)) ≫
        f.pushforward.map ((forgetAlgebraSheafInverseImageIso J K f A).inv.app
          ((freeAlgebraSheaf.{v', u', w'} K A).obj X)) := by
  change ((freeAlgebraSheafAdjunction.{v', u', w'} K A).comp
    (Under.postAdjunctionLeft (X := A) f.ringAdjunction)).unit.app X ≫ _ = _
  rw [Adjunction.comp_unit_app]
  change (_ ≫ (sheafCompose K (forget CommRingCat)).map (f.ringAdjunction.unit.app _)) ≫ 𝟙 _ = _
  rw [MorphismOfTopoi.ringAdjunction_unit_forget, Category.comp_id]
  change _ ≫ _ = _ ≫ _ ≫ f.pushforward.map (𝟙 _)
  rw [f.pushforward.map_id]
  exact congrArg (fun k => (freeAlgebraSheafAdjunction.{v', u', w'} K A).unit.app X ≫ k)
    (Category.comp_id _).symm

/-- **The square of Stacks 08SV.** The inverse image of the free `A`-algebra sheaf on a sheaf of
sets is the free `f⁻¹A`-algebra sheaf on its inverse image. -/
@[implicit_reducible]
noncomputable def freeAlgebraSheafInverseImageIso :
    freeAlgebraSheaf.{v', u', w'} K A ⋙ Under.post (X := A) f.inverseImageRing ≅
      f.inverseImage ⋙ freeAlgebraSheaf.{v, u, w} J (f.inverseImageRing.obj A) :=
  Adjunction.leftAdjointUniq (freeAlgebraSheafInverseImageAdjunction J K f A)
    (f.adj.comp (freeAlgebraSheafAdjunction.{v, u, w} J (f.inverseImageRing.obj A)))

/-- The comparison of the free algebra functors carries the unit of the free–forgetful adjunction
on the target to the unit on the source. With `forgetAlgebraSheafInverseImageIso` this is the
commuting square of adjunctions which the source's proof of Tag 08SV exhibits. -/
lemma freeAlgebraSheafInverseImageIso_unit (X : Sheaf K (Type (max u' v' w'))) :
    f.inverseImage.map ((freeAlgebraSheafAdjunction.{v', u', w'} K A).unit.app X) ≫
        (forgetAlgebraSheafInverseImageIso J K f A).inv.app
          ((freeAlgebraSheaf.{v', u', w'} K A).obj X) ≫
        (forgetAlgebraSheaf.{v, u, w} J (f.inverseImageRing.obj A)).map
          ((freeAlgebraSheafInverseImageIso J K f A).hom.app X) =
      (freeAlgebraSheafAdjunction.{v, u, w} J (f.inverseImageRing.obj A)).unit.app
        (f.inverseImage.obj X) := by
  apply (f.adj.homEquiv _ _).injective
  have he := Adjunction.unit_leftAdjointUniq_hom_app
    (freeAlgebraSheafInverseImageAdjunction J K f A)
    (f.adj.comp (freeAlgebraSheafAdjunction.{v, u, w} J (f.inverseImageRing.obj A))) X
  rw [Adjunction.comp_unit_app f.adj
    (freeAlgebraSheafAdjunction.{v, u, w} J (f.inverseImageRing.obj A)) X,
    freeAlgebraSheafInverseImageAdjunction_unit] at he
  simp only [Adjunction.homEquiv_apply, Functor.map_comp]
  rw [← Category.assoc, ← Category.assoc, f.adj.unit_naturality]
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Category.assoc] at he ⊢
  exact he

/-- The comparison of the two free–forgetful comonads whose iterates are the terms of the
standard resolution. -/
@[implicit_reducible]
noncomputable def standardResolutionComonadInverseImageIso :
    (standardResolutionComonad.{v', u', w'} K A : Under A ⥤ Under A) ⋙
        Under.post (X := A) f.inverseImageRing ≅
      Under.post (X := A) f.inverseImageRing ⋙
        (standardResolutionComonad.{v, u, w} J (f.inverseImageRing.obj A) :
          Under (f.inverseImageRing.obj A) ⥤ Under (f.inverseImageRing.obj A)) :=
  Adjunction.comonadSquareIso (F := freeAlgebraSheaf.{v', u', w'} K A)
    (U := forgetAlgebraSheaf.{v', u', w'} K A)
    (F' := freeAlgebraSheaf.{v, u, w} J (f.inverseImageRing.obj A))
    (U' := forgetAlgebraSheaf.{v, u, w} J (f.inverseImageRing.obj A))
    (L := f.inverseImage) (H := Under.post (X := A) f.inverseImageRing)
    (freeAlgebraSheafInverseImageIso J K f A) (forgetAlgebraSheafInverseImageIso J K f A)

end FreeAlgebraComparison

end CategoryTheory.Sheaf

end
