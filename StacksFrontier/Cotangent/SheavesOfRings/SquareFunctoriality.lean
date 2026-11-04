module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Cotangent.SheavesOfRings.InverseImageStandardResolution
public import StacksFrontier.Cotangent.SheavesOfRings.SectionsCotangentComparison
public import StacksFrontier.Cotangent.SheavesOfRings.TargetModulesTransport

/-!
# Square functoriality of the cotangent complex of a map of sheaves of rings

For a commutative square `a : A ⟶ A'`, `b : B ⟶ B'` between homomorphisms `f : A ⟶ B` and
`f' : A' ⟶ B'` of sheaves of commutative rings on a site, the free–forgetful comonads on the
sheaves of `A`-algebras and of `A'`-algebras are compared along restriction of scalars; iterating
that comparison produces a map `P_• ⟶ P'_•` of the two standard resolutions, and transposing the
universal derivations produces the induced `B`-linear map of cotangent complexes
`L_{B/A} ⟶ L_{B'/A'}`.

## Main definitions

* `CategoryTheory.Adjunction.comonadSquareHom` compares the two comonads attached to a square of
  adjunctions whose right adjoints commute.
* `CategoryTheory.Functor.iterateCompHom` and `CategoryTheory.Functor.iterateCompHomObj` iterate
  a comparison of commuting endofunctors.
* `CategoryTheory.SimplicialObject.homCompOfFacesAndDegeneracies` builds a morphism of simplicial
  objects into one pushed along a functor, from degreewise morphisms commuting with the faces and
  the degeneracies. It is the composite-valued form of
  `CategoryTheory.SimplicialObject.homOfFacesAndDegeneracies`, which this module takes from
  `StacksFrontier.Cotangent.SheavesOfRings.SectionsCotangentComparison` rather than redefining.
* `CategoryTheory.Sheaf.standardResolutionComonadSquareHom` is the comparison of the two
  free–forgetful comonads attached to `a : A ⟶ A'`.
* `CategoryTheory.Sheaf.squareResolutionMap` is the induced map `P_• ⟶ P'_•` of the standard
  resolutions, and `CategoryTheory.Sheaf.resolutionSquareMap` packages it with its three
  compatibilities.
* `CategoryTheory.Sheaf.squareCotangentTermMap`,
  `CategoryTheory.Sheaf.squareCotangentSimplicialMap` and
  `CategoryTheory.Sheaf.squareCotangentComplexMap` are the induced maps of base-changed sheaves
  of differentials, of simplicial modules and of cotangent complexes.
* `CategoryTheory.Sheaf.ResolutionSquareMap.symm`, `CategoryTheory.Sheaf.squareRestrictUnit` and
  `CategoryTheory.Sheaf.squareCotangentTermMapInv` are the inverse data available when the square
  is an isomorphism of arrows, and `CategoryTheory.Sheaf.squareCotangentComplexIso` is the
  resulting isomorphism of cotangent complexes.

## Main results

* `CategoryTheory.Sheaf.standardResolutionComonadSquareHom_counit` and
  `CategoryTheory.Sheaf.standardResolutionComonadSquareHom_comul`: the comonad comparison
  commutes with the counits and with the comultiplications. These are the two compatibilities
  that the inverse-image development leaves open for
  `CategoryTheory.Sheaf.standardResolutionComonadInverseImageIso`, and they are what makes the
  map of standard resolutions a construction rather than a hypothesis.
* `CategoryTheory.Sheaf.squareResolutionTermMap_augmentation`: the map of standard resolutions
  is compatible with the two augmentations in every degree.
* `CategoryTheory.Sheaf.squareCotangentComplexMap_derivation`: the map of complexes carries the
  universal derivation of `P_n` to that of `P'_n` precomposed with `P_n ⟶ P'_n`.
* `CategoryTheory.Adjunction.isIso_comonadSquareHom_app`: the comparison of comonads along an
  equivalence is an isomorphism, obtained by exhibiting it as the conjugate of the identification
  of the two right adjoints.
* `CategoryTheory.Sheaf.isIso_squareCotangentComplexMap`: **the invertibility lemma.** For an
  isomorphism of arrows the induced map of cotangent complexes is an isomorphism.

## Implementation notes

The comparison of comonads is the mate of the identification of the two forgetful functors: a
sheaf of `A'`-algebras read over `A` along `a` has the same underlying sheaf of sets, so
`Under.map a ⋙ forgetAlgebraSheaf J A` is `forgetAlgebraSheaf J A'` by reflexivity, and the
comparison `A[Z] ⟶ A'[Z]` is the transpose of the unit of the free–forgetful adjunction over
`A'`. Its compatibility with the counit and with the comultiplication is proved at abstract
types, by transposing both sides through the adjunction over `A`.

The comparison is a morphism rather than an isomorphism, so the iterate and simplicial-assembly
machinery of
`StacksFrontier.Cotangent.SheavesOfRings.InverseImageStandardResolutionComparison` cannot be reused;
`CategoryTheory.Functor.iterateCompHom` and
`CategoryTheory.SimplicialObject.homCompOfFacesAndDegeneracies` are its morphism-valued analogues,
with the opposite handedness, since here the functor is applied to the target of the comparison.
The underlying assembly of a simplicial morphism from degreewise data,
`CategoryTheory.SimplicialObject.homOfFacesAndDegeneracies`, is imported from
`StacksFrontier.Cotangent.SheavesOfRings.SectionsCotangentComparison`, which proves exactly the same
statement; this module deliberately does not restate it.
`CategoryTheory.Functor.iterateCompHomObj` additionally absorbs the morphism `B ⟶ B'` of the
square: the degree-`n` term of the resolution of `f` is the `(n+1)`-fold iterate at `B`, not at
`B'`, so the iterated comparison is preceded by the iterate of that morphism.

The target of the map of complexes is the cotangent complex of the right-hand column, read over
`B` by restriction of scalars along `b`: that is what `B`-linearity of a map into a complex of
`B'`-modules means. Restriction of scalars is additive, so it acts on complexes and commutes with
the alternating-face-map complex and with the reindexing of `HomologicalComplex.extend`.

Invertibility is proved degreewise and then propagated. The comparison of comonads is invertible
because, `Under.map a` being an equivalence for an isomorphism `a`, it is the conjugate of an
isomorphism of right adjoints, and conjugation preserves isomorphisms
(`CategoryTheory.conjugateEquiv_symm_iso`); the iterates and the morphism `B ⟶ B'` of the square
are then invertible degreewise. At the module level the inverse is the degreewise map of the
inverse square, read back over `B` through `CategoryTheory.Sheaf.squareRestrictUnit`: the two
composites are identified by the universal property of the base-changed differentials, the
retraction obtained from the inverse square forcing the second one.

The site-object and site-morphism universes are independent of the universe of sections, as in
`CategoryTheory.Sheaf.cotangentComplex`; the four sheaves of rings share the sections universe,
the square being over one site.

## References

* [Stacks Project, Tag 08SS](https://stacks.math.columbia.edu/tag/08SS)
* [Stacks Project, Tag 08SR](https://stacks.math.columbia.edu/tag/08SR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace CategoryTheory

universe v₁ u₁ v₂ u₂ v₃ u₃

/-! ## The comparison of comonads attached to a square of adjunctions -/

section AdjointSquare

variable {S : Type u₁} [Category.{v₁} S] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {F : S ⥤ D} {U : D ⥤ S} {F' : S ⥤ E} {U' : E ⥤ S} {K : E ⥤ D}

/-- The comparison of the comonads `U ⋙ F` and `U' ⋙ F'` along a functor `K` identifying the two
right adjoints: the transpose of the unit of the second adjunction. -/
def Adjunction.comonadSquareHom (adj : F ⊣ U) (adj' : F' ⊣ U') (i : K ⋙ U ≅ U') :
    K ⋙ (U ⋙ F) ⟶ (U' ⋙ F') ⋙ K where
  app Z := (adj.homEquiv (U.obj (K.obj Z)) (K.obj (F'.obj (U'.obj Z)))).symm
    (i.hom.app Z ≫ adj'.unit.app (U'.obj Z) ≫ i.inv.app (F'.obj (U'.obj Z)))
  naturality Z W g := by
    dsimp only [Functor.comp_map, Functor.comp_obj]
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have h1 := i.hom.naturality g
    have h2 := adj'.unit.naturality (U'.map g)
    have h3 := i.inv.naturality (F'.map (U'.map g))
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at h1 h2 h3
    simp only [Category.assoc]
    rw [← h3, ← Category.assoc (adj'.unit.app (U'.obj Z)), ← h2,
      ← Category.assoc (U.map (K.map g)), h1]
    simp only [Category.assoc]

/-- The transpose of the comparison of comonads is the unit of the second adjunction, read through
the identification of the two right adjoints. -/
lemma Adjunction.unit_comp_map_comonadSquareHom (adj : F ⊣ U) (adj' : F' ⊣ U')
    (i : K ⋙ U ≅ U') (Z : E) :
    adj.unit.app (U.obj (K.obj Z)) ≫
        U.map ((Adjunction.comonadSquareHom adj adj' i).app Z) =
      i.hom.app Z ≫ adj'.unit.app (U'.obj Z) ≫ i.inv.app (F'.obj (U'.obj Z)) :=
  (adj.homEquiv_unit _ _ _).symm.trans ((adj.homEquiv _ _).apply_symm_apply _)

/-- The comparison of comonads commutes with the counits of the two adjunctions. -/
lemma Adjunction.comonadSquareHom_counit (adj : F ⊣ U) (adj' : F' ⊣ U') (i : K ⋙ U ≅ U')
    (Z : E) :
    (Adjunction.comonadSquareHom adj adj' i).app Z ≫ K.map (adj'.counit.app Z) =
      adj.counit.app (K.obj Z) := by
  apply (adj.homEquiv (U.obj (K.obj Z)) (K.obj Z)).injective
  rw [adj.homEquiv_unit, adj.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  rw [adj.unit_comp_map_comonadSquareHom adj' i Z, adj.right_triangle_components]
  have h3 := i.inv.naturality (adj'.counit.app Z)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at h3
  simp only [Category.assoc]
  rw [← h3, ← Category.assoc (adj'.unit.app (U'.obj Z)), adj'.right_triangle_components]
  simp

/-- The comparison of comonads commutes with the comultiplications of the two comonads. -/
lemma Adjunction.comonadSquareHom_comul (adj : F ⊣ U) (adj' : F' ⊣ U') (i : K ⋙ U ≅ U')
    (Z : E) :
    F.map (adj.unit.app (U.obj (K.obj Z))) ≫
        F.map (U.map ((Adjunction.comonadSquareHom adj adj' i).app Z)) ≫
          (Adjunction.comonadSquareHom adj adj' i).app (F'.obj (U'.obj Z)) =
      (Adjunction.comonadSquareHom adj adj' i).app Z ≫
        K.map (F'.map (adj'.unit.app (U'.obj Z))) := by
  apply (adj.homEquiv _ _).injective
  rw [← Category.assoc, ← Functor.map_comp, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right, adj.homEquiv_unit, adj.homEquiv_unit]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [adj.unit_comp_map_comonadSquareHom adj' i (F'.obj (U'.obj Z)),
    adj.unit_comp_map_comonadSquareHom adj' i Z]
  have h3 := i.inv.naturality (F'.map (adj'.unit.app (U'.obj Z)))
  have h2 := adj'.unit.naturality (adj'.unit.app (U'.obj Z))
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at h2 h3
  simp only [Category.assoc]
  rw [← h3, ← Category.assoc (adj'.unit.app (U'.obj Z)) (U'.map _), ← h2,
    i.inv_hom_id_app_assoc]
  simp only [Category.assoc]

/-! ### Invertibility of the comparison along an equivalence -/

variable (eqv : E ≌ D)

/-- When the two right adjoints are identified along an equivalence, the right adjoint of
`F' ⋙ K` is identified with `U`. -/
@[simps! hom_app]
noncomputable def Adjunction.squareRightAdjointIso (i : eqv.functor ⋙ U ≅ U') :
    eqv.inverse ⋙ U' ≅ U :=
  NatIso.ofComponents
    (fun X => (i.app (eqv.inverse.obj X)).symm ≪≫ U.mapIso (eqv.counitIso.app X))
    (by
      intro X Y g
      have h := i.inv.naturality (eqv.inverse.map g)
      have hc := eqv.counitIso.hom.naturality g
      dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at h hc
      dsimp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom, Iso.app_hom,
        Functor.comp_map, Functor.comp_obj]
      rw [← Category.assoc, h, Category.assoc, ← U.map_comp, hc, U.map_comp, Category.assoc])

/-- The identification of the right adjoints transposes the unit of the adjunction
`F' ⋙ K ⊣ K⁻¹ ⋙ U'` into the unit of `F' ⊣ U'`. -/
lemma Adjunction.unit_comp_squareRightAdjointIso (adj' : F' ⊣ U')
    (i : eqv.functor ⋙ U ≅ U') (X : S) :
    (adj'.comp eqv.toAdjunction).unit.app X ≫
        (Adjunction.squareRightAdjointIso eqv i).hom.app ((F' ⋙ eqv.functor).obj X) =
      adj'.unit.app X ≫ i.inv.app (F'.obj X) := by
  have h3 := i.inv.naturality (eqv.unitIso.hom.app (F'.obj X))
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at h3
  have hu : eqv.toAdjunction.unit.app (F'.obj X) = eqv.unitIso.hom.app (F'.obj X) := rfl
  rw [Adjunction.comp_unit_app, Adjunction.squareRightAdjointIso_hom_app, hu]
  dsimp only [Functor.comp_obj]
  rw [Category.assoc, ← Category.assoc (U'.map _), h3, Category.assoc, ← U.map_comp,
    Equivalence.functor_unitIso_comp]
  simp

/-- The comparison of comonads is the conjugate of the identification of the right adjoints,
composed with the identification of the two forgetful images. -/
lemma Adjunction.comonadSquareHom_app_eq (adj : F ⊣ U) (adj' : F' ⊣ U')
    (i : eqv.functor ⋙ U ≅ U') (Z : E) :
    (Adjunction.comonadSquareHom adj adj' i).app Z =
      ((conjugateEquiv (adj'.comp eqv.toAdjunction) adj).symm
          (Adjunction.squareRightAdjointIso eqv i).hom).app
          (U.obj (eqv.functor.obj Z)) ≫
        eqv.functor.map (F'.map (i.hom.app Z)) := by
  apply (adj.homEquiv (U.obj (eqv.functor.obj Z))
    (eqv.functor.obj (F'.obj (U'.obj Z)))).injective
  rw [adj.homEquiv_unit, adj.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  rw [adj.unit_comp_map_comonadSquareHom adj' i Z,
    ← unit_conjugateEquiv_symm (adj'.comp eqv.toAdjunction) adj
      (Adjunction.squareRightAdjointIso eqv i).hom (U.obj (eqv.functor.obj Z)),
    Adjunction.unit_comp_squareRightAdjointIso eqv adj' i]
  have h3 := i.inv.naturality (F'.map (i.hom.app Z))
  have h2 := adj'.unit.naturality (i.hom.app Z)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at h2 h3
  simp only [Category.assoc]
  rw [← h3, ← Category.assoc, h2, Category.assoc]

/-- **The comparison of comonads along an equivalence is an isomorphism.** -/
instance Adjunction.isIso_comonadSquareHom_app (adj : F ⊣ U) (adj' : F' ⊣ U')
    (i : eqv.functor ⋙ U ≅ U') (Z : E) :
    IsIso ((Adjunction.comonadSquareHom adj adj' i).app Z) := by
  rw [Adjunction.comonadSquareHom_app_eq eqv adj adj' i Z]
  infer_instance

end AdjointSquare

/-! ## Iterating a comparison of commuting endofunctors -/

section Iterate

variable {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]
  {G : D ⥤ D} {G' : E ⥤ E} {K : E ⥤ D}

/-- A comparison `K ⋙ G ⟶ G' ⋙ K` of commuting endofunctors, iterated `n` times. -/
def Functor.iterateCompHom (e : K ⋙ G ⟶ G' ⋙ K) :
    (n : ℕ) → (K ⋙ G.iterate n ⟶ G'.iterate n ⋙ K)
  | 0 => 𝟙 K
  | n + 1 => Functor.whiskerRight (Functor.iterateCompHom e n) G ≫
      Functor.whiskerLeft (G'.iterate n) e

/-- The components of the iterated comparison in degree zero. -/
lemma Functor.iterateCompHom_zero_app (e : K ⋙ G ⟶ G' ⋙ K) (Z : E) :
    (Functor.iterateCompHom e 0).app Z = 𝟙 (K.obj Z) := rfl

/-- The recursion satisfied by the components of the iterated comparison. -/
lemma Functor.iterateCompHom_succ_app (e : K ⋙ G ⟶ G' ⋙ K) (n : ℕ) (Z : E) :
    (Functor.iterateCompHom e (n + 1)).app Z =
      G.map ((Functor.iterateCompHom e n).app Z) ≫ e.app ((G'.iterate n).obj Z) := rfl

/-- Each component of the iterated comparison is an isomorphism when every component of `e` is. -/
instance Functor.isIso_iterateCompHom_app (e : K ⋙ G ⟶ G' ⋙ K) [∀ Z, IsIso (e.app Z)]
    (n : ℕ) (Z : E) : IsIso ((Functor.iterateCompHom e n).app Z) := by
  induction n generalizing Z with
  | zero => exact inferInstanceAs (IsIso (𝟙 (K.obj Z)))
  | succ n ih =>
    rw [Functor.iterateCompHom_succ_app]
    have := ih Z
    infer_instance

/-- The iterated comparison commutes with Godement's face maps. -/
lemma Functor.iterateCompHom_godementFace (e : K ⋙ G ⟶ G' ⋙ K) (ε : G ⟶ 𝟭 D) (ε' : G' ⟶ 𝟭 E)
    (hε : ∀ Z, e.app Z ≫ K.map (ε'.app Z) = ε.app (K.obj Z))
    (n : ℕ) (j : Fin (n + 1)) (Z : E) :
    (Godement.face ε n j).app (K.obj Z) ≫ (Functor.iterateCompHom e n).app Z =
      (Functor.iterateCompHom e (n + 1)).app Z ≫ K.map ((Godement.face ε' n j).app Z) := by
  induction n generalizing Z with
  | zero =>
    simpa [Godement.face, Functor.iterateCompHom, Functor.iterate] using (hε Z).symm
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Godement.Prep.face_zero, Functor.whiskerLeft_app]
      have hn := ε.naturality ((Functor.iterateCompHom e (n + 1)).app Z)
      dsimp only [Functor.id_map, Functor.comp_obj] at hn
      rw [Functor.iterateCompHom_succ_app (n := n + 1), Category.assoc, hε, ← hn]
    · simp only [Godement.Prep.face_succ, Functor.whiskerRight_app]
      have hn := e.naturality ((Godement.face ε' n j).app Z)
      dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
      rw [Functor.iterateCompHom_succ_app, Functor.iterateCompHom_succ_app (n := n + 1),
        ← Category.assoc, ← G.map_comp, ih j Z, G.map_comp, Category.assoc, hn,
        Category.assoc]

/-- The iterated comparison commutes with Godement's degeneracy maps. -/
lemma Functor.iterateCompHom_godementDegeneracy (e : K ⋙ G ⟶ G' ⋙ K) (δ : G ⟶ G ⋙ G)
    (δ' : G' ⟶ G' ⋙ G')
    (hδ : ∀ Z, δ.app (K.obj Z) ≫ G.map (e.app Z) ≫ e.app (G'.obj Z) =
      e.app Z ≫ K.map (δ'.app Z))
    (n : ℕ) (j : Fin (n + 1)) (Z : E) :
    (Godement.degeneracy δ n j).app (K.obj Z) ≫ (Functor.iterateCompHom e (n + 2)).app Z =
      (Functor.iterateCompHom e (n + 1)).app Z ≫
        K.map ((Godement.degeneracy δ' n j).app Z) := by
  induction n generalizing Z with
  | zero =>
    simpa [Godement.degeneracy, Functor.iterateCompHom, Functor.iterate] using hδ Z
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Godement.Prep.degeneracy_zero, Functor.whiskerLeft_app]
      have hn := δ.naturality ((Functor.iterateCompHom e (n + 1)).app Z)
      dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
      rw [Functor.iterateCompHom_succ_app (n := n + 2),
        Functor.iterateCompHom_succ_app (n := n + 1), Functor.map_comp, ← Category.assoc,
        ← Category.assoc, ← hn]
      simp only [Category.assoc]
      exact congrArg (fun k => G.map ((Functor.iterateCompHom e (n + 1)).app Z) ≫ k)
        (hδ ((G'.iterate (n + 1)).obj Z))
    · simp only [Godement.Prep.degeneracy_succ, Functor.whiskerRight_app]
      have hn := e.naturality ((Godement.degeneracy δ' n j).app Z)
      dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
      rw [Functor.iterateCompHom_succ_app (n := n + 2), ← Category.assoc, ← G.map_comp,
        ih j Z, G.map_comp, Category.assoc, hn,
        Functor.iterateCompHom_succ_app (n := n + 1), Category.assoc]

/-- The iterated comparison, read at an object of the source presented through a morphism
`u : X ⟶ K.obj Z`. -/
def Functor.iterateCompHomObj (e : K ⋙ G ⟶ G' ⋙ K) (n : ℕ) {X : D} {Z : E} (u : X ⟶ K.obj Z) :
    (G.iterate n).obj X ⟶ K.obj ((G'.iterate n).obj Z) :=
  (G.iterate n).map u ≫ (Functor.iterateCompHom e n).app Z

/-- The transported iterated comparison is an isomorphism when `u` and every component of `e`
are. -/
instance Functor.isIso_iterateCompHomObj (e : K ⋙ G ⟶ G' ⋙ K) [∀ Z, IsIso (e.app Z)]
    (n : ℕ) {X : D} {Z : E} (u : X ⟶ K.obj Z) [IsIso u] :
    IsIso (Functor.iterateCompHomObj e n u) := by
  rw [Functor.iterateCompHomObj]
  infer_instance

/-- A natural transformation between iterates of `G` and `G'` compatible with the iterated
comparison is still compatible after transporting along `u`. -/
private lemma iterateCompHomObj_of_comp_eq (e : K ⋙ G ⟶ G' ⋙ K) {p q : ℕ}
    (τ : G.iterate p ⟶ G.iterate q) (τ' : G'.iterate p ⟶ G'.iterate q) {X : D} {Z : E}
    (h : τ.app (K.obj Z) ≫ (Functor.iterateCompHom e q).app Z =
      (Functor.iterateCompHom e p).app Z ≫ K.map (τ'.app Z))
    (u : X ⟶ K.obj Z) :
    τ.app X ≫ Functor.iterateCompHomObj e q u =
      Functor.iterateCompHomObj e p u ≫ K.map (τ'.app Z) := by
  rw [Functor.iterateCompHomObj, Functor.iterateCompHomObj, Category.assoc, ← h,
    ← Category.assoc, ← τ.naturality u, Category.assoc]

/-- The transported iterated comparison commutes with Godement's face maps. -/
lemma Functor.iterateCompHomObj_godementFace (e : K ⋙ G ⟶ G' ⋙ K) (ε : G ⟶ 𝟭 D) (ε' : G' ⟶ 𝟭 E)
    (hε : ∀ Z, e.app Z ≫ K.map (ε'.app Z) = ε.app (K.obj Z))
    (n : ℕ) (j : Fin (n + 1)) {X : D} {Z : E} (u : X ⟶ K.obj Z) :
    (Godement.face ε n j).app X ≫ Functor.iterateCompHomObj e n u =
      Functor.iterateCompHomObj e (n + 1) u ≫ K.map ((Godement.face ε' n j).app Z) :=
  iterateCompHomObj_of_comp_eq e _ _
    (Functor.iterateCompHom_godementFace e ε ε' hε n j Z) u

/-- The transported iterated comparison commutes with Godement's degeneracy maps. -/
lemma Functor.iterateCompHomObj_godementDegeneracy (e : K ⋙ G ⟶ G' ⋙ K) (δ : G ⟶ G ⋙ G)
    (δ' : G' ⟶ G' ⋙ G')
    (hδ : ∀ Z, δ.app (K.obj Z) ≫ G.map (e.app Z) ≫ e.app (G'.obj Z) =
      e.app Z ≫ K.map (δ'.app Z))
    (n : ℕ) (j : Fin (n + 1)) {X : D} {Z : E} (u : X ⟶ K.obj Z) :
    (Godement.degeneracy δ n j).app X ≫ Functor.iterateCompHomObj e (n + 2) u =
      Functor.iterateCompHomObj e (n + 1) u ≫
        K.map ((Godement.degeneracy δ' n j).app Z) :=
  iterateCompHomObj_of_comp_eq e _ _
    (Functor.iterateCompHom_godementDegeneracy e δ δ' hδ n j Z) u

/-- At the first iterate the transported comparison still commutes with the given counits. -/
lemma Functor.iterateCompHomObj_one_counit (e : K ⋙ G ⟶ G' ⋙ K) (ε : G ⟶ 𝟭 D) (ε' : G' ⟶ 𝟭 E)
    (hε : ∀ Z, e.app Z ≫ K.map (ε'.app Z) = ε.app (K.obj Z))
    {X : D} {Z : E} (u : X ⟶ K.obj Z) :
    Functor.iterateCompHomObj e 1 u ≫ K.map (ε'.app Z) = ε.app X ≫ u := by
  have hn := ε.naturality u
  dsimp only [Functor.id_map] at hn
  have h1 : Functor.iterateCompHomObj e 1 u = G.map u ≫ e.app Z := by
    simp [Functor.iterateCompHomObj, Functor.iterateCompHom, Functor.iterate]
  rw [h1, Category.assoc, hε]
  exact hn

/-- A morphism into the image of a functor, transported along equalities of its source and of the
argument of the functor. -/
def Functor.transportObjHom (K : E ⥤ D) {X X' : D} {Y Y' : E} (p : X = X') (q : Y = Y')
    (φ : X' ⟶ K.obj Y') : X ⟶ K.obj Y :=
  eqToHom p ≫ φ ≫ K.map (eqToHom q.symm)

/-- The transport of an isomorphism is an isomorphism. -/
instance Functor.isIso_transportObjHom (K : E ⥤ D) {X X' : D} {Y Y' : E} (p : X = X')
    (q : Y = Y') (φ : X' ⟶ K.obj Y') [IsIso φ] :
    IsIso (Functor.transportObjHom K p q φ) := by
  rw [Functor.transportObjHom]
  infer_instance

/-- Transported morphisms are natural for morphisms which are the transports of a naturality
square for the untransported ones. -/
lemma Functor.transportObjHom_naturality (K : E ⥤ D)
    {X₁ X₁' X₂ X₂' : D} {Y₁ Y₁' Y₂ Y₂' : E}
    (p₁ : X₁ = X₁') (p₂ : X₂ = X₂') (q₁ : Y₁ = Y₁') (q₂ : Y₂ = Y₂')
    (φ₁ : X₁' ⟶ K.obj Y₁') (φ₂ : X₂' ⟶ K.obj Y₂')
    {α : X₁ ⟶ X₂} {α' : X₁' ⟶ X₂'} {β : Y₁ ⟶ Y₂} {β' : Y₁' ⟶ Y₂'}
    (hα : α = eqToHom p₁ ≫ α' ≫ eqToHom p₂.symm)
    (hβ : β = eqToHom q₁ ≫ β' ≫ eqToHom q₂.symm)
    (h : α' ≫ φ₂ = φ₁ ≫ K.map β') :
    α ≫ Functor.transportObjHom K p₂ q₂ φ₂ =
      Functor.transportObjHom K p₁ q₁ φ₁ ≫ K.map β := by
  subst p₁ p₂ q₁ q₂
  simpa [Functor.transportObjHom, hα, hβ] using h

/-- The transported comparison of the first iterates carries the counit presentation of one
augmentation to the counit presentation of the other. -/
lemma Functor.transportObjHom_comp_counit (e : K ⋙ G ⟶ G' ⋙ K) (ε : G ⟶ 𝟭 D) (ε' : G' ⟶ 𝟭 E)
    (hε : ∀ Z, e.app Z ≫ K.map (ε'.app Z) = ε.app (K.obj Z))
    {X₁ : D} {Y₁ : E} {X : D} {Z : E} (u : X ⟶ K.obj Z)
    (p : X₁ = (G.iterate 1).obj X) (q : Y₁ = (G'.iterate 1).obj Z)
    {m : X₁ ⟶ X} {k : Y₁ ⟶ Z}
    (hm : m = eqToHom p ≫ ε.app X) (hk : k = eqToHom q ≫ ε'.app Z) :
    Functor.transportObjHom K p q (Functor.iterateCompHomObj e 1 u) ≫ K.map k = m ≫ u := by
  subst p q hm hk
  simpa [Functor.transportObjHom] using Functor.iterateCompHomObj_one_counit e ε ε' hε u

end Iterate

/-! ## Assembling a morphism of simplicial objects -/

section Simplicial

variable {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]

/-- Degreewise morphisms into a simplicial object pushed along a functor, commuting with every
face and every degeneracy map, assemble into a morphism of simplicial objects. -/
def SimplicialObject.homCompOfFacesAndDegeneracies (K : E ⥤ D) (X : SimplicialObject D)
    (Y : SimplicialObject E) (e : ∀ n, X.obj (op ⦋n⦌) ⟶ K.obj (Y.obj (op ⦋n⦌)))
    (hδ : ∀ n (j : Fin (n + 2)), X.δ j ≫ e n = e (n + 1) ≫ K.map (Y.δ j))
    (hσ : ∀ n (j : Fin (n + 1)), X.σ j ≫ e (n + 1) = e n ≫ K.map (Y.σ j)) :
    X ⟶ Y ⋙ K :=
  SimplicialObject.homOfFacesAndDegeneracies (X := X) (Y := Y ⋙ K) e hδ hσ

/-- The components of `SimplicialObject.homCompOfFacesAndDegeneracies` are the given degreewise
morphisms. -/
lemma SimplicialObject.homCompOfFacesAndDegeneracies_app (K : E ⥤ D) (X : SimplicialObject D)
    (Y : SimplicialObject E) (e : ∀ n, X.obj (op ⦋n⦌) ⟶ K.obj (Y.obj (op ⦋n⦌)))
    (hδ : ∀ n (j : Fin (n + 2)), X.δ j ≫ e n = e (n + 1) ≫ K.map (Y.δ j))
    (hσ : ∀ n (j : Fin (n + 1)), X.σ j ≫ e (n + 1) = e n ≫ K.map (Y.σ j)) (n : ℕ) :
    (SimplicialObject.homCompOfFacesAndDegeneracies K X Y e hδ hσ).app (op ⦋n⦌) = e n := rfl

/-- A morphism of simplicial objects compatible in degree zero with two morphisms to constant
objects is compatible with them in every degree. -/
lemma SimplicialObject.hom_comp_mapToConst_of_zero (K : E ⥤ D) {X : SimplicialObject D}
    {Y : SimplicialObject E} {X₀ : D} {Y₀ : E}
    (α : X ⟶ (SimplicialObject.const D).obj X₀)
    (β : Y ⟶ (SimplicialObject.const E).obj Y₀) (φ : X ⟶ Y ⋙ K) (c : X₀ ⟶ K.obj Y₀)
    (h₀ : φ.app (op ⦋0⦌) ≫ K.map (β.app (op ⦋0⦌)) = α.app (op ⦋0⦌) ≫ c)
    (n : ℕ) : φ.app (op ⦋n⦌) ≫ K.map (β.app (op ⦋n⦌)) = α.app (op ⦋n⦌) ≫ c := by
  induction n with
  | zero => exact h₀
  | succ n ih =>
    have ha : X.map (SimplexCategory.δ (0 : Fin (n + 2))).op ≫ α.app (op ⦋n⦌) =
        α.app (op ⦋n + 1⦌) :=
      (α.naturality (SimplexCategory.δ (0 : Fin (n + 2))).op).trans (Category.comp_id _)
    have hb : Y.map (SimplexCategory.δ (0 : Fin (n + 2))).op ≫ β.app (op ⦋n⦌) =
        β.app (op ⦋n + 1⦌) :=
      (β.naturality (SimplexCategory.δ (0 : Fin (n + 2))).op).trans (Category.comp_id _)
    have hf := φ.naturality (SimplexCategory.δ (0 : Fin (n + 2))).op
    dsimp only [Functor.comp_map] at hf
    rw [← hb, K.map_comp, ← Category.assoc, ← hf, Category.assoc, ih, ← Category.assoc, ha]

end Simplicial

end CategoryTheory

namespace CategoryTheory.Sheaf

universe u v w

section Comonad

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A A' : Sheaf J CommRingCat.{max u v w}}

/-- Sheaves of `A'`-algebras read as sheaves of `A`-algebras along `a : A ⟶ A'`. -/
noncomputable abbrev squareAlgebras (a : A ⟶ A') : Under A' ⥤ Under A := Under.map a

/-- Reading a sheaf of `A'`-algebras over `A` does not change its underlying sheaf of sets. -/
lemma squareAlgebras_comp_forgetAlgebraSheaf (a : A ⟶ A') :
    squareAlgebras J a ⋙ forgetAlgebraSheaf.{v, u, w} J A =
      forgetAlgebraSheaf.{v, u, w} J A' :=
  rfl

/-- The comparison of the two free–forgetful comonads attached to `a : A ⟶ A'`: the morphism of
sheaves of `A`-algebras `A[Z] ⟶ A'[Z]` transposing the unit of the free–forgetful adjunction
over `A'`. -/
@[implicit_reducible]
noncomputable def standardResolutionComonadSquareHom (a : A ⟶ A') :
    squareAlgebras J a ⋙ (standardResolutionComonad.{v, u, w} J A : Under A ⥤ Under A) ⟶
      (standardResolutionComonad.{v, u, w} J A' : Under A' ⥤ Under A') ⋙ squareAlgebras J a :=
  Adjunction.comonadSquareHom (F := freeAlgebraSheaf.{v, u, w} J A)
    (U := forgetAlgebraSheaf.{v, u, w} J A) (F' := freeAlgebraSheaf.{v, u, w} J A')
    (U' := forgetAlgebraSheaf.{v, u, w} J A') (K := squareAlgebras J a)
    (freeAlgebraSheafAdjunction.{v, u, w} J A) (freeAlgebraSheafAdjunction.{v, u, w} J A')
    (Iso.refl _)

/-- The comparison of the two free–forgetful comonads commutes with their counits. -/
lemma standardResolutionComonadSquareHom_counit (a : A ⟶ A') (Z : Under A') :
    (standardResolutionComonadSquareHom.{u, v, w} J a).app Z ≫
        (squareAlgebras J a).map ((standardResolutionComonad.{v, u, w} J A').ε.app Z) =
      (standardResolutionComonad.{v, u, w} J A).ε.app ((squareAlgebras J a).obj Z) :=
  Adjunction.comonadSquareHom_counit (F := freeAlgebraSheaf.{v, u, w} J A)
    (U := forgetAlgebraSheaf.{v, u, w} J A) (F' := freeAlgebraSheaf.{v, u, w} J A')
    (U' := forgetAlgebraSheaf.{v, u, w} J A') (K := squareAlgebras J a)
    (freeAlgebraSheafAdjunction.{v, u, w} J A) (freeAlgebraSheafAdjunction.{v, u, w} J A')
    (Iso.refl _) Z

/-- The comparison of the two free–forgetful comonads commutes with their
comultiplications. -/
lemma standardResolutionComonadSquareHom_comul (a : A ⟶ A') (Z : Under A') :
    (standardResolutionComonad.{v, u, w} J A).δ.app ((squareAlgebras J a).obj Z) ≫
        (standardResolutionComonad.{v, u, w} J A : Under A ⥤ Under A).map
            ((standardResolutionComonadSquareHom.{u, v, w} J a).app Z) ≫
          (standardResolutionComonadSquareHom.{u, v, w} J a).app
            ((standardResolutionComonad.{v, u, w} J A' : Under A' ⥤ Under A').obj Z) =
      (standardResolutionComonadSquareHom.{u, v, w} J a).app Z ≫
        (squareAlgebras J a).map ((standardResolutionComonad.{v, u, w} J A').δ.app Z) :=
  Adjunction.comonadSquareHom_comul (F := freeAlgebraSheaf.{v, u, w} J A)
    (U := forgetAlgebraSheaf.{v, u, w} J A) (F' := freeAlgebraSheaf.{v, u, w} J A')
    (U' := forgetAlgebraSheaf.{v, u, w} J A') (K := squareAlgebras J a)
    (freeAlgebraSheafAdjunction.{v, u, w} J A) (freeAlgebraSheafAdjunction.{v, u, w} J A')
    (Iso.refl _) Z

end Comonad

section Resolution

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A A' B B' : Sheaf J CommRingCat.{max u v w}} {f : A ⟶ B} {f' : A' ⟶ B'}

/-- The right-hand edge `b : B ⟶ B'` of a commutative square, read as a morphism of sheaves of
`A`-algebras. -/
noncomputable def squareAlgebraMap (a : A ⟶ A') (b : B ⟶ B') (hsq : f ≫ b = a ≫ f') :
    Under.mk f ⟶ (squareAlgebras J a).obj (Under.mk f') :=
  Under.homMk b hsq

/-- The map `P_n ⟶ P'_n` of the degree-`n` terms of the two standard resolutions induced by a
commutative square: the `(n+1)`-fold iterate of the comparison of comonads, applied to the
right-hand edge of the square. -/
noncomputable def squareResolutionTermMap (a : A ⟶ A') (b : B ⟶ B') (hsq : f ≫ b = a ≫ f')
    (n : ℕ) :
    (standardResolution.{v, u, w} J f).left.obj (op ⦋n⦌) ⟶
      (squareAlgebras J a).obj ((standardResolution.{v, u, w} J f').left.obj (op ⦋n⦌)) :=
  Functor.transportObjHom (squareAlgebras J a)
    (standardResolution_obj.{v, u, w} J f n) (standardResolution_obj.{v, u, w} J f' n)
    (Functor.iterateCompHomObj (standardResolutionComonadSquareHom.{u, v, w} J a) (n + 1)
      (squareAlgebraMap.{u, v, w} J a b hsq))

/-- The termwise map commutes with the face maps of the two standard resolutions. -/
lemma squareResolutionTermMap_delta (a : A ⟶ A') (b : B ⟶ B') (hsq : f ≫ b = a ≫ f')
    (n : ℕ) (j : Fin (n + 2)) :
    (standardResolution.{v, u, w} J f).left.δ j ≫
        squareResolutionTermMap.{u, v, w} J a b hsq n =
      squareResolutionTermMap.{u, v, w} J a b hsq (n + 1) ≫
        (squareAlgebras J a).map ((standardResolution.{v, u, w} J f').left.δ j) :=
  Functor.transportObjHom_naturality (squareAlgebras J a)
    (standardResolution_obj.{v, u, w} J f (n + 1)) (standardResolution_obj.{v, u, w} J f n)
    (standardResolution_obj.{v, u, w} J f' (n + 1)) (standardResolution_obj.{v, u, w} J f' n)
    (Functor.iterateCompHomObj (standardResolutionComonadSquareHom.{u, v, w} J a) (n + 2)
      (squareAlgebraMap.{u, v, w} J a b hsq))
    (Functor.iterateCompHomObj (standardResolutionComonadSquareHom.{u, v, w} J a) (n + 1)
      (squareAlgebraMap.{u, v, w} J a b hsq))
    (standardResolution_delta.{u, v, w} J f n j)
    (standardResolution_delta.{u, v, w} J f' n j)
    (Functor.iterateCompHomObj_godementFace
      (standardResolutionComonadSquareHom.{u, v, w} J a)
      (standardResolutionComonad.{v, u, w} J A).ε
      (standardResolutionComonad.{v, u, w} J A').ε
      (standardResolutionComonadSquareHom_counit.{u, v, w} J a) (n + 1) j
      (squareAlgebraMap.{u, v, w} J a b hsq))

/-- The termwise map commutes with the degeneracy maps of the two standard resolutions. -/
lemma squareResolutionTermMap_sigma (a : A ⟶ A') (b : B ⟶ B') (hsq : f ≫ b = a ≫ f')
    (n : ℕ) (j : Fin (n + 1)) :
    (standardResolution.{v, u, w} J f).left.σ j ≫
        squareResolutionTermMap.{u, v, w} J a b hsq (n + 1) =
      squareResolutionTermMap.{u, v, w} J a b hsq n ≫
        (squareAlgebras J a).map ((standardResolution.{v, u, w} J f').left.σ j) :=
  Functor.transportObjHom_naturality (squareAlgebras J a)
    (standardResolution_obj.{v, u, w} J f n) (standardResolution_obj.{v, u, w} J f (n + 1))
    (standardResolution_obj.{v, u, w} J f' n) (standardResolution_obj.{v, u, w} J f' (n + 1))
    (Functor.iterateCompHomObj (standardResolutionComonadSquareHom.{u, v, w} J a) (n + 1)
      (squareAlgebraMap.{u, v, w} J a b hsq))
    (Functor.iterateCompHomObj (standardResolutionComonadSquareHom.{u, v, w} J a) (n + 2)
      (squareAlgebraMap.{u, v, w} J a b hsq))
    (standardResolution_sigma.{u, v, w} J f n j)
    (standardResolution_sigma.{u, v, w} J f' n j)
    (Functor.iterateCompHomObj_godementDegeneracy
      (standardResolutionComonadSquareHom.{u, v, w} J a)
      (standardResolutionComonad.{v, u, w} J A).δ
      (standardResolutionComonad.{v, u, w} J A').δ
      (standardResolutionComonadSquareHom_comul.{u, v, w} J a) n j
      (squareAlgebraMap.{u, v, w} J a b hsq))

/-- The map `P_• ⟶ P'_•` of the two standard resolutions induced by a commutative square of
homomorphisms of sheaves of commutative rings. -/
noncomputable def squareResolutionMap (a : A ⟶ A') (b : B ⟶ B') (hsq : f ≫ b = a ≫ f') :
    (standardResolution.{v, u, w} J f).left ⟶
      (standardResolution.{v, u, w} J f').left ⋙ squareAlgebras J a :=
  SimplicialObject.homCompOfFacesAndDegeneracies (squareAlgebras J a)
    (standardResolution.{v, u, w} J f).left (standardResolution.{v, u, w} J f').left
    (squareResolutionTermMap.{u, v, w} J a b hsq)
    (squareResolutionTermMap_delta.{u, v, w} J a b hsq)
    (squareResolutionTermMap_sigma.{u, v, w} J a b hsq)

/-- The components of the map of standard resolutions are the termwise maps. -/
lemma squareResolutionMap_app (a : A ⟶ A') (b : B ⟶ B') (hsq : f ≫ b = a ≫ f') (n : ℕ) :
    (squareResolutionMap.{u, v, w} J a b hsq).app (op ⦋n⦌) =
      squareResolutionTermMap.{u, v, w} J a b hsq n :=
  rfl

/-- In degree zero the termwise map is compatible with the two augmentations. -/
lemma squareResolutionTermMap_augmentation_zero (a : A ⟶ A') (b : B ⟶ B')
    (hsq : f ≫ b = a ≫ f') :
    squareResolutionTermMap.{u, v, w} J a b hsq 0 ≫
        (squareAlgebras J a).map ((standardResolution.{v, u, w} J f').hom.app (op ⦋0⦌)) =
      (standardResolution.{v, u, w} J f).hom.app (op ⦋0⦌) ≫
        squareAlgebraMap.{u, v, w} J a b hsq :=
  Functor.transportObjHom_comp_counit (standardResolutionComonadSquareHom.{u, v, w} J a)
    (standardResolutionComonad.{v, u, w} J A).ε (standardResolutionComonad.{v, u, w} J A').ε
    (standardResolutionComonadSquareHom_counit.{u, v, w} J a)
    (squareAlgebraMap.{u, v, w} J a b hsq)
    (standardResolution_obj.{v, u, w} J f 0) (standardResolution_obj.{v, u, w} J f' 0)
    (standardResolution_augmentation_app_zero.{u, v, w} J f)
    (standardResolution_augmentation_app_zero.{u, v, w} J f')

/-- The map of standard resolutions is compatible with the two augmentations in every degree. -/
lemma squareResolutionTermMap_augmentation (a : A ⟶ A') (b : B ⟶ B') (hsq : f ≫ b = a ≫ f')
    (n : ℕ) :
    squareResolutionTermMap.{u, v, w} J a b hsq n ≫
        (squareAlgebras J a).map ((standardResolution.{v, u, w} J f').hom.app (op ⦋n⦌)) =
      (standardResolution.{v, u, w} J f).hom.app (op ⦋n⦌) ≫
        squareAlgebraMap.{u, v, w} J a b hsq :=
  SimplicialObject.hom_comp_mapToConst_of_zero (squareAlgebras J a)
    (standardResolution.{v, u, w} J f).hom (standardResolution.{v, u, w} J f').hom
    (squareResolutionMap.{u, v, w} J a b hsq) (squareAlgebraMap.{u, v, w} J a b hsq)
    (squareResolutionTermMap_augmentation_zero.{u, v, w} J a b hsq) n

/-- When the base map is an isomorphism, the comparison of the two free–forgetful comonads is an
isomorphism. -/
instance isIso_standardResolutionComonadSquareHom_app (a : A ⟶ A') [IsIso a] (Z : Under A') :
    IsIso ((standardResolutionComonadSquareHom.{u, v, w} J a).app Z) :=
  Adjunction.isIso_comonadSquareHom_app (F := freeAlgebraSheaf.{v, u, w} J A)
    (U := forgetAlgebraSheaf.{v, u, w} J A) (F' := freeAlgebraSheaf.{v, u, w} J A')
    (U' := forgetAlgebraSheaf.{v, u, w} J A') (Under.mapIso (asIso a))
    (freeAlgebraSheafAdjunction.{v, u, w} J A) (freeAlgebraSheafAdjunction.{v, u, w} J A')
    (Iso.refl _) Z

/-- When the right-hand edge of the square is an isomorphism, so is the induced morphism of
sheaves of `A`-algebras. -/
instance isIso_squareAlgebraMap (a : A ⟶ A') (b : B ⟶ B') (hsq : f ≫ b = a ≫ f') [IsIso b] :
    IsIso (squareAlgebraMap.{u, v, w} J a b hsq) := by
  have h : IsIso ((Under.forget A).map (squareAlgebraMap.{u, v, w} J a b hsq)) :=
    inferInstanceAs (IsIso b)
  exact isIso_of_reflects_iso _ (Under.forget A)

/-- For an isomorphism of arrows the termwise map of standard resolutions is an
isomorphism. -/
instance isIso_squareResolutionTermMap (a : A ⟶ A') (b : B ⟶ B') (hsq : f ≫ b = a ≫ f')
    [IsIso a] [IsIso b] (n : ℕ) :
    IsIso (squareResolutionTermMap.{u, v, w} J a b hsq n) := by
  rw [squareResolutionTermMap]
  infer_instance

end Resolution

section Modules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A A' B B' : Sheaf J CommRingCat.{max u v w}} {f : A ⟶ B} {f' : A' ⟶ B'}

/-- A map of the two standard resolutions over a commutative square `A ⟶ A'`, `B ⟶ B'` of
homomorphisms of sheaves of commutative rings: a degreewise homomorphism `P_n ⟶ P'_n`,
simplicial and compatible with the maps from the base sheaves and with the two
augmentations. -/
structure ResolutionSquareMap (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B') where
  /-- The homomorphism `P_n ⟶ P'_n` in simplicial degree `n`. -/
  resolution (n : SimplexCategoryᵒᵖ) :
    resolutionTerm.{u, v, w} J f n ⟶ resolutionTerm.{u, v, w} J f' n
  /-- It is compatible with the maps from the two base sheaves. -/
  resolution_base (n : SimplexCategoryᵒᵖ) :
    resolutionBase.{u, v, w} J f n ≫ resolution n = a ≫ resolutionBase.{u, v, w} J f' n
  /-- It is compatible with the two augmentations. -/
  resolution_augmentation (n : SimplexCategoryᵒᵖ) :
    resolution n ≫ resolutionAugmentation.{u, v, w} J f' n =
      resolutionAugmentation.{u, v, w} J f n ≫ b
  /-- It is a map of simplicial sheaves of rings. -/
  resolution_naturality {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j) :
    ((standardResolution.{v, u, w} J f).left.map g).right ≫ resolution j =
      resolution i ≫ ((standardResolution.{v, u, w} J f').left.map g).right

/-- The canonical map of standard resolutions attached to a commutative square of homomorphisms
of sheaves of commutative rings. -/
noncomputable def resolutionSquareMap (a : A ⟶ A') (b : B ⟶ B') (hsq : f ≫ b = a ≫ f') :
    ResolutionSquareMap.{u, v, w} J f f' a b where
  resolution n := ((squareResolutionMap.{u, v, w} J a b hsq).app n).right
  resolution_base n := Under.w ((squareResolutionMap.{u, v, w} J a b hsq).app n)
  resolution_augmentation n := congrArg Under.Hom.right
    (squareResolutionTermMap_augmentation.{u, v, w} J a b hsq n.unop.len)
  resolution_naturality g := congrArg Under.Hom.right
    ((squareResolutionMap.{u, v, w} J a b hsq).naturality g)

/-- For an isomorphism of arrows the canonical map of standard resolutions is an isomorphism in
every simplicial degree. -/
instance isIso_resolutionSquareMap_resolution (a : A ⟶ A') (b : B ⟶ B')
    (hsq : f ≫ b = a ≫ f') [IsIso a] [IsIso b] (n : SimplexCategoryᵒᵖ) :
    IsIso ((resolutionSquareMap.{u, v, w} J a b hsq).resolution n) := by
  have h : (resolutionSquareMap.{u, v, w} J a b hsq).resolution n =
      (Under.forget A).map
        (squareResolutionTermMap.{u, v, w} J a b hsq n.unop.len) := rfl
  rw [h]
  exact Functor.map_isIso (Under.forget A)
    (squareResolutionTermMap.{u, v, w} J a b hsq n.unop.len)

namespace ResolutionSquareMap

variable {J} {a : A ⟶ A'} {b : B ⟶ B'}

/-- Equal morphisms of sheaves of rings agree on sections. -/
private lemma hom_app_congr {X Y : Sheaf J CommRingCat.{max u v w}} {k l : X ⟶ Y} (h : k = l)
    (U : Cᵒᵖ) (x : X.obj.obj U) : k.hom.app U x = l.hom.app U x := by
  rw [h]

/-- Compatibility with the base sheaves, on sections. -/
lemma resolution_base_app (sq : ResolutionSquareMap.{u, v, w} J f f' a b)
    (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) (x : A.obj.obj U) :
    (sq.resolution n).hom.app U ((resolutionBase.{u, v, w} J f n).hom.app U x) =
      (resolutionBase.{u, v, w} J f' n).hom.app U (a.hom.app U x) :=
  hom_app_congr (sq.resolution_base n) U x

/-- Compatibility with the augmentations, on sections. -/
lemma resolution_augmentation_app (sq : ResolutionSquareMap.{u, v, w} J f f' a b)
    (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) (x : (resolutionTerm.{u, v, w} J f n).obj.obj U) :
    (resolutionAugmentation.{u, v, w} J f' n).hom.app U ((sq.resolution n).hom.app U x) =
      b.hom.app U ((resolutionAugmentation.{u, v, w} J f n).hom.app U x) :=
  hom_app_congr (sq.resolution_augmentation n) U x

/-- Compatibility with the simplicial operators, on sections. -/
lemma resolution_naturality_app (sq : ResolutionSquareMap.{u, v, w} J f f' a b)
    {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j) (U : Cᵒᵖ)
    (x : (resolutionTerm.{u, v, w} J f i).obj.obj U) :
    (sq.resolution j).hom.app U
        (((standardResolution.{v, u, w} J f).left.map g).right.hom.app U x) =
      ((standardResolution.{v, u, w} J f').left.map g).right.hom.app U
        ((sq.resolution i).hom.app U x) :=
  hom_app_congr (sq.resolution_naturality g) U x

/-- The inverse of an isomorphism of arrows, as a map of the standard resolutions in the
opposite direction. -/
noncomputable def symm (sq : ResolutionSquareMap.{u, v, w} J f f' a b) [IsIso a] [IsIso b]
    (h : ∀ n, IsIso (sq.resolution n)) :
    ResolutionSquareMap.{u, v, w} J f' f (CategoryTheory.inv a) (CategoryTheory.inv b) where
  resolution n := have := h n; CategoryTheory.inv (sq.resolution n)
  resolution_base n := by
    have := h n
    rw [IsIso.comp_inv_eq, Category.assoc, sq.resolution_base n, ← Category.assoc,
      IsIso.inv_hom_id, Category.id_comp]
  resolution_augmentation n := by
    have := h n
    rw [IsIso.inv_comp_eq, ← Category.assoc, sq.resolution_augmentation n, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  resolution_naturality {i j} g := by
    have := h i
    have := h j
    rw [IsIso.comp_inv_eq, Category.assoc, sq.resolution_naturality g, ← Category.assoc,
      IsIso.inv_hom_id, Category.id_comp]

/-- The degreewise maps of the two mutually inverse squares cancel, on sections. -/
lemma symm_resolution_app (sq : ResolutionSquareMap.{u, v, w} J f f' a b) [IsIso a] [IsIso b]
    (h : ∀ n, IsIso (sq.resolution n)) (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ)
    (x : (resolutionTerm.{u, v, w} J f n).obj.obj U) :
    ((sq.symm h).resolution n).hom.app U ((sq.resolution n).hom.app U x) = x := by
  have := h n
  exact hom_app_congr (IsIso.hom_inv_id (sq.resolution n)) U x

/-- The degreewise maps of the two mutually inverse squares cancel in the other order, on
sections. -/
lemma symm_resolution_app' (sq : ResolutionSquareMap.{u, v, w} J f f' a b) [IsIso a] [IsIso b]
    (h : ∀ n, IsIso (sq.resolution n)) (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ)
    (y : (resolutionTerm.{u, v, w} J f' n).obj.obj U) :
    (sq.resolution n).hom.app U (((sq.symm h).resolution n).hom.app U y) = y := by
  have := h n
  exact hom_app_congr (IsIso.inv_hom_id (sq.resolution n)) U y

end ResolutionSquareMap

/-- The homomorphism of the target sheaves of rings underlying `b : B ⟶ B'`. -/
noncomputable abbrev squareTargetRing (b : B ⟶ B') :
    Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B' :=
  (sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).map b

/-- Sheaves of `B'`-modules read as sheaves of `B`-modules along `b : B ⟶ B'`. -/
noncomputable abbrev squareRestrict (b : B ⟶ B') :
    targetModules.{u, v, w} J B' ⥤ targetModules.{u, v, w} J B :=
  SheafOfModules.restrictScalars (squareTargetRing.{u, v, w} J b)

/-- Undoing the two restrictions of scalars along an isomorphism `b : B ⟶ B'` and its inverse:
restricting along `b⁻¹` and then along `b` returns the original sheaf of `B`-modules. -/
noncomputable def squareRestrictUnit (b : B ⟶ B') [IsIso b] (M : targetModules.{u, v, w} J B) :
    (squareRestrict.{u, v, w} J b).obj
        ((squareRestrict.{u, v, w} J (CategoryTheory.inv b)).obj M) ≅ M :=
  ((targetModulesTransport.{u, v, w} J (asIso b)).unitIso.app M).symm

/-- Undoing the two restrictions of scalars in the other order. -/
noncomputable def squareRestrictCounit (b : B ⟶ B') [IsIso b]
    (M : targetModules.{u, v, w} J B') :
    (squareRestrict.{u, v, w} J (CategoryTheory.inv b)).obj
        ((squareRestrict.{u, v, w} J b).obj M) ≅ M :=
  (targetModulesTransport.{u, v, w} J (asIso b)).counitIso.app M

attribute [local instance] moduleOfSections

variable {J} {a : A ⟶ A'} {b : B ⟶ B'}

/-- Two derivations of `P_n` agree when they agree on sections. -/
private lemma resolutionDerivations_ext {n : SimplexCategoryᵒᵖ} {M : targetModules.{u, v, w} J B}
    {D₁ D₂ : resolutionDerivations.{u, v, w} J f n M}
    (h : ∀ (U : Cᵒᵖ) (x : (resolutionTerm.{u, v, w} J f n).obj.obj U), D₁.d x = D₂.d x) :
    D₁ = D₂ :=
  PresheafOfModules.Derivation.ext (funext fun U => AddMonoidHom.ext (h U))

/-- Precomposition of an `A'`-derivation of `P'_n` with the map `P_n ⟶ P'_n` of the standard
resolutions over a square is an `A`-derivation of `P_n`, valued in the target module read over
`B` along `b`. -/
noncomputable def squareDerivation (sq : ResolutionSquareMap.{u, v, w} J f f' a b)
    (n : SimplexCategoryᵒᵖ) (M : targetModules.{u, v, w} J B')
    (D : resolutionDerivations.{u, v, w} J f' n M) :
    resolutionDerivations.{u, v, w} J f n ((squareRestrict.{u, v, w} J b).obj M) where
  d {U} := (D.d (X := U)).comp ((sq.resolution n).hom.app U).hom.toAddMonoidHom
  d_mul {U} x y := by
    change D.d ((sq.resolution n).hom.app U (x * y)) =
      b.hom.app U ((resolutionAugmentation.{u, v, w} J f n).hom.app U x) •
        (show M.val.obj U from D.d ((sq.resolution n).hom.app U y)) +
      b.hom.app U ((resolutionAugmentation.{u, v, w} J f n).hom.app U y) •
        (show M.val.obj U from D.d ((sq.resolution n).hom.app U x))
    rw [map_mul ((sq.resolution n).hom.app U).hom, D.d_mul]
    change (resolutionAugmentation.{u, v, w} J f' n).hom.app U
          ((sq.resolution n).hom.app U x) •
        (show M.val.obj U from D.d ((sq.resolution n).hom.app U y)) +
      (resolutionAugmentation.{u, v, w} J f' n).hom.app U ((sq.resolution n).hom.app U y) •
        (show M.val.obj U from D.d ((sq.resolution n).hom.app U x)) = _
    rw [sq.resolution_augmentation_app, sq.resolution_augmentation_app]
  d_map {U V} g x := by
    have h := congrArg (fun k => k x) ((sq.resolution n).hom.naturality g)
    dsimp at h
    change D.d ((sq.resolution n).hom.app V
        ((resolutionTerm.{u, v, w} J f n).obj.map g x)) =
      M.val.map g (D.d ((sq.resolution n).hom.app U x))
    rw [h]
    exact D.d_map g _
  d_app {U} x := by
    change D.d ((sq.resolution n).hom.app U
      ((resolutionBase.{u, v, w} J f n).hom.app U x)) = 0
    rw [sq.resolution_base_app]
    exact D.d_app _

/-- The derivation precomposed with `P_n ⟶ P'_n`, on sections. -/
lemma squareDerivation_d (sq : ResolutionSquareMap.{u, v, w} J f f' a b)
    (n : SimplexCategoryᵒᵖ) (M : targetModules.{u, v, w} J B')
    (D : resolutionDerivations.{u, v, w} J f' n M) (U : Cᵒᵖ)
    (x : (resolutionTerm.{u, v, w} J f n).obj.obj U) :
    (squareDerivation sq n M D).d x = D.d ((sq.resolution n).hom.app U x) :=
  rfl

/-- Precomposition with `P_n ⟶ P'_n` commutes with postcomposition by a map of coefficient
modules. -/
lemma squareDerivation_postcomp (sq : ResolutionSquareMap.{u, v, w} J f f' a b)
    (n : SimplexCategoryᵒᵖ) {M N : targetModules.{u, v, w} J B'}
    (D : resolutionDerivations.{u, v, w} J f' n M) (h : M ⟶ N) :
    (squareDerivation sq n M D).postcomp
        ((SheafOfModules.restrictScalars (resolutionAugmentationRing.{u, v, w} J f n)).map
          ((squareRestrict.{u, v, w} J b).map h)).val =
      squareDerivation sq n N (D.postcomp
        ((SheafOfModules.restrictScalars
          (resolutionAugmentationRing.{u, v, w} J f' n)).map h).val) :=
  resolutionDerivations_ext fun _ _ => rfl

/-- The map `Ω_{P_n/A} ⊗_{P_n} B ⟶ Ω_{P'_n/A'} ⊗_{P'_n} B'` of base-changed sheaves of
differentials induced by a commutative square: the morphism transposing the universal derivation
of `P'_n` precomposed with `P_n ⟶ P'_n`. -/
noncomputable def squareCotangentTermMap (sq : ResolutionSquareMap.{u, v, w} J f f' a b)
    (n : SimplexCategoryᵒᵖ) :
    (cotangentSimplicialModule.{u, v, w} J f).object.obj n ⟶
      (squareRestrict.{u, v, w} J b).obj
        ((cotangentSimplicialModule.{u, v, w} J f').object.obj n) :=
  ((cotangentSimplicialModule.{u, v, w} J f).derivationEquiv n _).symm
    (squareDerivation sq n _
      ((cotangentSimplicialModule.{u, v, w} J f').universalDerivation n))

/-- The degreewise map transposes precomposition with `P_n ⟶ P'_n`. -/
lemma squareCotangentTermMap_derivation (sq : ResolutionSquareMap.{u, v, w} J f f' a b)
    (n : SimplexCategoryᵒᵖ) :
    (cotangentSimplicialModule.{u, v, w} J f).derivationEquiv n _
        (squareCotangentTermMap sq n) =
      squareDerivation sq n _
        ((cotangentSimplicialModule.{u, v, w} J f').universalDerivation n) :=
  ((cotangentSimplicialModule.{u, v, w} J f).derivationEquiv n _).apply_symm_apply _

/-- On sections the degreewise map carries the universal derivation of `P_n` to the universal
derivation of `P'_n` precomposed with `P_n ⟶ P'_n`. -/
lemma squareCotangentTermMap_d (sq : ResolutionSquareMap.{u, v, w} J f f' a b)
    (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) (x : (resolutionTerm.{u, v, w} J f n).obj.obj U) :
    ((cotangentSimplicialModule.{u, v, w} J f).derivationEquiv n _
        (squareCotangentTermMap sq n)).d x =
      ((cotangentSimplicialModule.{u, v, w} J f').universalDerivation n).d
        ((sq.resolution n).hom.app U x) :=
  PresheafOfModules.Derivation.congr_d (X := U) (squareCotangentTermMap_derivation sq n) x

/-- The degreewise map is the unique morphism transposing precomposition with `P_n ⟶ P'_n`. -/
lemma squareCotangentTermMap_unique (sq : ResolutionSquareMap.{u, v, w} J f f' a b)
    (n : SimplexCategoryᵒᵖ)
    (φ : (cotangentSimplicialModule.{u, v, w} J f).object.obj n ⟶
      (squareRestrict.{u, v, w} J b).obj
        ((cotangentSimplicialModule.{u, v, w} J f').object.obj n))
    (hφ : ∀ (U : Cᵒᵖ) (x : (resolutionTerm.{u, v, w} J f n).obj.obj U),
      ((cotangentSimplicialModule.{u, v, w} J f).derivationEquiv n _ φ).d x =
        ((cotangentSimplicialModule.{u, v, w} J f').universalDerivation n).d
          ((sq.resolution n).hom.app U x)) :
    φ = squareCotangentTermMap sq n :=
  ((cotangentSimplicialModule.{u, v, w} J f).derivationEquiv n _).injective
    (resolutionDerivations_ext fun U x =>
      (hφ U x).trans (squareCotangentTermMap_d sq n U x).symm)

/-- The degreewise maps commute with every simplicial operator. -/
lemma squareCotangentTermMap_naturality (sq : ResolutionSquareMap.{u, v, w} J f f' a b)
    {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j) :
    (cotangentSimplicialModule.{u, v, w} J f).object.map g ≫ squareCotangentTermMap sq j =
      squareCotangentTermMap sq i ≫
        (squareRestrict.{u, v, w} J b).map
          ((cotangentSimplicialModule.{u, v, w} J f').object.map g) := by
  refine ((cotangentSimplicialModule.{u, v, w} J f).derivationEquiv i _).injective
    (resolutionDerivations_ext fun U x => ?_)
  rw [(cotangentSimplicialModule.{u, v, w} J f).simplex_naturality g _
      (squareCotangentTermMap sq j) U x,
    squareCotangentTermMap_derivation,
    (cotangentSimplicialModule.{u, v, w} J f).naturality i (squareCotangentTermMap sq i)
      ((squareRestrict.{u, v, w} J b).map
        ((cotangentSimplicialModule.{u, v, w} J f').object.map g)),
    squareCotangentTermMap_derivation, squareDerivation_postcomp,
    ← (cotangentSimplicialModule.{u, v, w} J f').derivationEquiv_eq_postcomp i
      ((cotangentSimplicialModule.{u, v, w} J f').object.map g),
    squareDerivation_d, squareDerivation_d, sq.resolution_naturality_app]
  have h0 := (cotangentSimplicialModule.{u, v, w} J f').simplex_naturality g
    ((cotangentSimplicialModule.{u, v, w} J f').object.obj j) (𝟙 _) U
    ((sq.resolution i).hom.app U x)
  rw [Category.comp_id] at h0
  exact h0.symm

/-- The map of simplicial `B`-modules induced by a commutative square, the target read over `B`
along `b`. -/
noncomputable def squareCotangentSimplicialMap
    (sq : ResolutionSquareMap.{u, v, w} J f f' a b) :
    (cotangentSimplicialModule.{u, v, w} J f).object ⟶
      ((SimplicialObject.whiskering _ _).obj (squareRestrict.{u, v, w} J b)).obj
        (cotangentSimplicialModule.{u, v, w} J f').object where
  app n := squareCotangentTermMap sq n
  naturality _ _ g := squareCotangentTermMap_naturality sq g

/-- The induced map of alternating-face-map complexes, the target read over `B` along `b`. -/
noncomputable def squareCotangentMooreMap (sq : ResolutionSquareMap.{u, v, w} J f f' a b) :
    (AlgebraicTopology.alternatingFaceMapComplex (targetModules.{u, v, w} J B)).obj
        (cotangentSimplicialModule.{u, v, w} J f).object ⟶
      ((squareRestrict.{u, v, w} J b).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((AlgebraicTopology.alternatingFaceMapComplex (targetModules.{u, v, w} J B')).obj
          (cotangentSimplicialModule.{u, v, w} J f').object) :=
  (AlgebraicTopology.alternatingFaceMapComplex (targetModules.{u, v, w} J B)).map
      (squareCotangentSimplicialMap sq) ≫
    ((AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
        (squareRestrict.{u, v, w} J b)).app
      (cotangentSimplicialModule.{u, v, w} J f').object).inv

/-- In degree `n` the map of alternating-face-map complexes is the degreewise map. -/
@[simp]
lemma squareCotangentMooreMap_f (sq : ResolutionSquareMap.{u, v, w} J f f' a b) (n : ℕ) :
    (squareCotangentMooreMap sq).f n = squareCotangentTermMap sq (op ⦋n⦌) :=
  Category.comp_id _

/-- The `B`-linear map of cotangent complexes `L_{B/A} ⟶ L_{B'/A'}` induced by a commutative
square of homomorphisms of sheaves of commutative rings. -/
noncomputable def squareCotangentComplexMap
    (sq : ResolutionSquareMap.{u, v, w} J f f' a b) :
    cotangentComplex.{u, v, w} J f ⟶
      ((squareRestrict.{u, v, w} J b).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (cotangentComplex.{u, v, w} J f') :=
  HomologicalComplex.extendMap (squareCotangentMooreMap sq)
      (ComplexShape.embeddingUpIntLE 0) ≫
    (HomologicalComplex.mapHomologicalComplexExtendIso (squareRestrict.{u, v, w} J b)
      ((AlgebraicTopology.alternatingFaceMapComplex (targetModules.{u, v, w} J B')).obj
        (cotangentSimplicialModule.{u, v, w} J f').object)
      (ComplexShape.embeddingUpIntLE 0)).hom

/-- In cohomological degree `-n` the map of cotangent complexes is the degreewise map of
base-changed differentials, read through the two canonical degree isomorphisms. -/
lemma squareCotangentComplexMap_f (sq : ResolutionSquareMap.{u, v, w} J f f' a b) (n : ℕ) :
    (squareCotangentComplexMap sq).f (-(n : ℤ)) =
      (cotangentComplex_degreeIso.{u, v, w} J f n).hom ≫
        squareCotangentTermMap sq (op ⦋n⦌) ≫
          (squareRestrict.{u, v, w} J b).map
            (cotangentComplex_degreeIso.{u, v, w} J f' n).inv := by
  have h : (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = -(n : ℤ) := by simp
  simp only [squareCotangentComplexMap, cotangentComplex,
    HomologicalComplex.extendMap_mapHomologicalComplexExtendIso_f _ _ _ _ h,
    squareCotangentMooreMap_f, cotangentComplex_degreeIso]

/-- The map of cotangent complexes carries the universal derivation of `P_n` to the universal
derivation of `P'_n` precomposed with the map `P_n ⟶ P'_n` of the standard resolutions: this is
the sheaf-level form of `1 ⊗ d p ↦ 1 ⊗ d (u p)`. -/
lemma squareCotangentComplexMap_derivation (sq : ResolutionSquareMap.{u, v, w} J f f' a b)
    (n : ℕ) (U : Cᵒᵖ) (x : (resolutionTerm.{u, v, w} J f (op ⦋n⦌)).obj.obj U) :
    ((cotangentSimplicialModule.{u, v, w} J f).derivationEquiv (op ⦋n⦌) _
        ((cotangentComplex_degreeIso.{u, v, w} J f n).inv ≫
          (squareCotangentComplexMap sq).f (-(n : ℤ)) ≫
            (squareRestrict.{u, v, w} J b).map
              (cotangentComplex_degreeIso.{u, v, w} J f' n).hom)).d x =
      ((cotangentSimplicialModule.{u, v, w} J f').universalDerivation (op ⦋n⦌)).d
        ((sq.resolution (op ⦋n⦌)).hom.app U x) := by
  have h : (cotangentComplex_degreeIso.{u, v, w} J f n).inv ≫
      (squareCotangentComplexMap sq).f (-(n : ℤ)) ≫
        (squareRestrict.{u, v, w} J b).map
          (cotangentComplex_degreeIso.{u, v, w} J f' n).hom =
      squareCotangentTermMap sq (op ⦋n⦌) := by
    rw [squareCotangentComplexMap_f]
    simp [← Functor.map_comp]
  rw [h, squareCotangentTermMap_d]

/-! ### Invertibility for an isomorphism of arrows -/

/-- The derivation corepresented by the degreewise map followed by a map of coefficients:
precomposition with `P_n ⟶ P'_n`, postcomposed with that map. -/
lemma squareCotangentTermMap_comp_derivation (sq : ResolutionSquareMap.{u, v, w} J f f' a b)
    (n : SimplexCategoryᵒᵖ) {M : targetModules.{u, v, w} J B}
    (g : (squareRestrict.{u, v, w} J b).obj
      ((cotangentSimplicialModule.{u, v, w} J f').object.obj n) ⟶ M) :
    (cotangentSimplicialModule.{u, v, w} J f).derivationEquiv n M
        (squareCotangentTermMap sq n ≫ g) =
      (squareDerivation sq n _
          ((cotangentSimplicialModule.{u, v, w} J f').universalDerivation n)).postcomp
        (((SheafOfModules.restrictScalars
          (resolutionAugmentationRing.{u, v, w} J f n)).map g).val) := by
  rw [(cotangentSimplicialModule.{u, v, w} J f).naturality n (squareCotangentTermMap sq n) g,
    squareCotangentTermMap_derivation]

/-- Two maps of standard resolutions over mutually inverse squares whose degreewise maps cancel
induce maps of base-changed differentials which cancel, once the two restrictions of scalars are
undone by a morphism which is the identity on sections. -/
lemma squareCotangentTermMap_comp_eq_id {a₂ : A' ⟶ A} {b₂ : B' ⟶ B}
    (sq : ResolutionSquareMap.{u, v, w} J f f' a b)
    (sq' : ResolutionSquareMap.{u, v, w} J f' f a₂ b₂) (n : SimplexCategoryᵒᵖ)
    (c : (squareRestrict.{u, v, w} J b).obj ((squareRestrict.{u, v, w} J b₂).obj
        ((cotangentSimplicialModule.{u, v, w} J f).object.obj n)) ⟶
      (cotangentSimplicialModule.{u, v, w} J f).object.obj n)
    (hc : ∀ (U : Cᵒᵖ) (y : ((cotangentSimplicialModule.{u, v, w} J f).object.obj n).val.obj U),
      (c.val.app U).hom y = y)
    (hcancel : ∀ (U : Cᵒᵖ) (x : (resolutionTerm.{u, v, w} J f n).obj.obj U),
      (sq'.resolution n).hom.app U ((sq.resolution n).hom.app U x) = x) :
    squareCotangentTermMap sq n ≫
        (squareRestrict.{u, v, w} J b).map (squareCotangentTermMap sq' n) ≫ c = 𝟙 _ := by
  refine ((cotangentSimplicialModule.{u, v, w} J f).derivationEquiv n _).injective ?_
  rw [squareCotangentTermMap_comp_derivation sq n
    ((squareRestrict.{u, v, w} J b).map (squareCotangentTermMap sq' n) ≫ c)]
  refine resolutionDerivations_ext fun U x => ?_
  have hψ := PresheafOfModules.Derivation.congr_d
    (squareCotangentTermMap_derivation sq' n) ((sq.resolution n).hom.app U x)
  rw [(cotangentSimplicialModule.{u, v, w} J f').derivationEquiv_eq_postcomp n
    (squareCotangentTermMap sq' n)] at hψ
  exact (hc U _).trans (hψ.trans (congrArg
    (fun z => ((cotangentSimplicialModule.{u, v, w} J f).universalDerivation n).d z)
    (hcancel U x)))

/-- The candidate inverse of the degreewise map of base-changed differentials for an isomorphism
of arrows: the degreewise map of the inverse square, read back over `B`. -/
noncomputable def squareCotangentTermMapInv (sq : ResolutionSquareMap.{u, v, w} J f f' a b)
    [IsIso a] [IsIso b] (h : ∀ n, IsIso (sq.resolution n)) (n : SimplexCategoryᵒᵖ) :
    (squareRestrict.{u, v, w} J b).obj
        ((cotangentSimplicialModule.{u, v, w} J f').object.obj n) ⟶
      (cotangentSimplicialModule.{u, v, w} J f).object.obj n :=
  (squareRestrict.{u, v, w} J b).map (squareCotangentTermMap (sq.symm h) n) ≫
    (squareRestrictUnit.{u, v, w} J b
      ((cotangentSimplicialModule.{u, v, w} J f).object.obj n)).hom

/-- **For an isomorphism of arrows the degreewise map of base-changed sheaves of differentials is
an isomorphism.** The degreewise map of the inverse square is a two-sided inverse, once the two
restrictions of scalars are undone. -/
lemma isIso_squareCotangentTermMap (sq : ResolutionSquareMap.{u, v, w} J f f' a b)
    [IsIso a] [IsIso b] (h : ∀ n, IsIso (sq.resolution n)) (n : SimplexCategoryᵒᵖ) :
    IsIso (squareCotangentTermMap sq n) := by
  have L1 : squareCotangentTermMap sq n ≫ squareCotangentTermMapInv sq h n = 𝟙 _ :=
    squareCotangentTermMap_comp_eq_id sq (sq.symm h) n
      (squareRestrictUnit.{u, v, w} J b
        ((cotangentSimplicialModule.{u, v, w} J f).object.obj n)).hom
      (fun _ _ => rfl) (sq.symm_resolution_app h n)
  have L2 : squareCotangentTermMap (sq.symm h) n ≫
      ((squareRestrict.{u, v, w} J (CategoryTheory.inv b)).map
          (squareCotangentTermMap sq n) ≫
        (squareRestrictCounit.{u, v, w} J b
          ((cotangentSimplicialModule.{u, v, w} J f').object.obj n)).hom) = 𝟙 _ :=
    squareCotangentTermMap_comp_eq_id (sq.symm h) sq n
      (squareRestrictCounit.{u, v, w} J b
        ((cotangentSimplicialModule.{u, v, w} J f').object.obj n)).hom
      (fun _ _ => rfl) (sq.symm_resolution_app' h n)
  obtain ⟨r, hr⟩ : ∃ r, squareCotangentTermMapInv sq h n ≫ r = 𝟙 _ :=
    ⟨(squareRestrictUnit.{u, v, w} J b
          ((cotangentSimplicialModule.{u, v, w} J f).object.obj n)).inv ≫
        (squareRestrict.{u, v, w} J b).map
          ((squareRestrict.{u, v, w} J (CategoryTheory.inv b)).map
              (squareCotangentTermMap sq n) ≫
            (squareRestrictCounit.{u, v, w} J b
              ((cotangentSimplicialModule.{u, v, w} J f').object.obj n)).hom), by
      rw [squareCotangentTermMapInv]
      simp only [Category.assoc]
      rw [← Category.assoc (squareRestrictUnit.{u, v, w} J b
          ((cotangentSimplicialModule.{u, v, w} J f).object.obj n)).hom,
        Iso.hom_inv_id, Category.id_comp, ← Functor.map_comp, L2, Functor.map_id]⟩
  have hrφ : r = squareCotangentTermMap sq n := by
    rw [← Category.id_comp r, ← L1, Category.assoc, hr, Category.comp_id]
  exact ⟨⟨squareCotangentTermMapInv sq h n, L1, hrφ ▸ hr⟩⟩

/-- For an isomorphism of arrows the induced map of simplicial `B`-modules is an
isomorphism. -/
lemma isIso_squareCotangentSimplicialMap (sq : ResolutionSquareMap.{u, v, w} J f f' a b)
    [IsIso a] [IsIso b] (h : ∀ n, IsIso (sq.resolution n)) :
    IsIso (squareCotangentSimplicialMap sq) := by
  have : ∀ n, IsIso ((squareCotangentSimplicialMap sq).app n) := fun n =>
    isIso_squareCotangentTermMap sq h n
  exact NatIso.isIso_of_isIso_app _

/-- For an isomorphism of arrows the induced map of alternating-face-map complexes is an
isomorphism. -/
lemma isIso_squareCotangentMooreMap (sq : ResolutionSquareMap.{u, v, w} J f f' a b)
    [IsIso a] [IsIso b] (h : ∀ n, IsIso (sq.resolution n)) :
    IsIso (squareCotangentMooreMap sq) := by
  have := isIso_squareCotangentSimplicialMap sq h
  rw [squareCotangentMooreMap]
  infer_instance

/-- For an isomorphism of arrows the induced isomorphism of cotangent complexes
`L_{B/A} ≅ L_{B'/A'}`, assembled from the degreewise isomorphisms of base-changed sheaves of
differentials. -/
noncomputable def squareCotangentComplexIsoOfSquare
    (sq : ResolutionSquareMap.{u, v, w} J f f' a b) [IsIso a] [IsIso b]
    (h : ∀ n, IsIso (sq.resolution n)) :
    cotangentComplex.{u, v, w} J f ≅
      ((squareRestrict.{u, v, w} J b).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (cotangentComplex.{u, v, w} J f') :=
  have := isIso_squareCotangentMooreMap sq h
  ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor
        (targetModules.{u, v, w} J B)).mapIso (asIso (squareCotangentMooreMap sq)) ≪≫
    HomologicalComplex.mapHomologicalComplexExtendIso (squareRestrict.{u, v, w} J b)
      ((AlgebraicTopology.alternatingFaceMapComplex (targetModules.{u, v, w} J B')).obj
        (cotangentSimplicialModule.{u, v, w} J f').object)
      (ComplexShape.embeddingUpIntLE 0)

/-- **The invertibility lemma.** For an isomorphism of arrows — that is, a commutative square
whose two horizontal edges are isomorphisms — the induced map of cotangent complexes
`L_{B/A} ⟶ L_{B'/A'}` is an isomorphism. -/
lemma isIso_squareCotangentComplexMap (sq : ResolutionSquareMap.{u, v, w} J f f' a b)
    [IsIso a] [IsIso b] (h : ∀ n, IsIso (sq.resolution n)) :
    IsIso (squareCotangentComplexMap sq) :=
  ⟨⟨(squareCotangentComplexIsoOfSquare sq h).inv,
    (squareCotangentComplexIsoOfSquare sq h).hom_inv_id,
    (squareCotangentComplexIsoOfSquare sq h).inv_hom_id⟩⟩

/-- **The invertibility lemma for the canonical map.** An isomorphism of arrows of sheaves of
commutative rings induces an isomorphism of cotangent complexes. -/
instance isIso_squareCotangentComplexMap_resolutionSquareMap (hsq : f ≫ b = a ≫ f')
    [IsIso a] [IsIso b] :
    IsIso (squareCotangentComplexMap (resolutionSquareMap.{u, v, w} J a b hsq)) :=
  isIso_squareCotangentComplexMap _ (fun _ => inferInstance)

/-- The isomorphism of cotangent complexes attached to an isomorphism of arrows of sheaves of
commutative rings. -/
noncomputable def squareCotangentComplexIso (hsq : f ≫ b = a ≫ f') [IsIso a] [IsIso b] :
    cotangentComplex.{u, v, w} J f ≅
      ((squareRestrict.{u, v, w} J b).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (cotangentComplex.{u, v, w} J f') :=
  squareCotangentComplexIsoOfSquare (resolutionSquareMap.{u, v, w} J a b hsq)
    (fun _ => inferInstance)

end Modules

end CategoryTheory.Sheaf
