module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Uniqueness of the representing pair of a representable category over `𝒞`

Stacks 02Y3 (2): if `p : 𝒮 ⥤ 𝒞` is representable by `X` via an equivalence `j : 𝒮 → 𝒞/X`
over `𝒞`, then the pair `(X, j)` is unique up to isomorphism. That is, for a second pair
`(X', j')` there is an isomorphism `φ : X' ≅ X` such that `j` is 2-isomorphic over `𝒞` to the
composite of `j'` with the slice functor `𝒞/X' ⥤ 𝒞/X` induced by `φ` (Mathlib's
`Over.map φ.hom`).

The isomorphism is `StacksRepresentableCFG.representing_object_unique`, and the
2-isomorphism over `𝒞` is `StacksRepresentableCFG.representingPairIso`. The key computation,
`StacksRepresentableCFG.over_hom_eq_of_comp_forget_eq`, is the Yoneda-type observation used in
the source's proof: a functor `F : 𝒞/X' ⥤ 𝒞/X` strictly over `𝒞` is postcomposition with the
structure morphism of `F (X', 𝟙)`.
-/

@[expose] public section

open CategoryTheory

namespace StacksRepresentableCFG

universe v u v' u'

variable {𝒮 : Type u} [Category.{v} 𝒮] {𝒞 : Type u'} [Category.{v'} 𝒞]

/-- A functor `F : 𝒞/X' ⥤ 𝒞/X` strictly over `𝒞` sends `t = (U, a)` to `(U, a ≫ ψ)`, where
`ψ` is the structure morphism of `F (X', 𝟙 X')` (up to the identifications of underlying
objects given by `hw`). -/
lemma over_hom_eq_of_comp_forget_eq {X X' : 𝒞} (F : Over X' ⥤ Over X)
    (hw : F ⋙ Over.forget X = Over.forget X') (t : Over X') :
    (F.obj t).hom = eqToHom (Functor.congr_obj hw t) ≫ t.hom ≫
      eqToHom (Functor.congr_obj hw (Over.mk (𝟙 X'))).symm ≫ (F.obj (Over.mk (𝟙 X'))).hom := by
  have hm := Functor.congr_hom hw (Over.homMk t.hom : t ⟶ Over.mk (𝟙 X'))
  simp only [Functor.comp_map, Over.forget_map, Over.homMk_left] at hm
  rw [← Over.w (F.map (Over.homMk t.hom : t ⟶ Over.mk (𝟙 X'))), hm]
  simp

/-- The structure morphism of `representing_object_unique p j j'`: it is the structure
morphism of the image of `(X', 𝟙 X')` under `j ∘ j'⁻¹ : 𝒞/X' ⥤ 𝒞/X`. -/
lemma representing_object_unique_hom (p : 𝒮 ⥤ 𝒞) {X X' : 𝒞}
    (j : EquivalenceOver (𝒞 := 𝒞) p (Over.forget X))
    (j' : EquivalenceOver (𝒞 := 𝒞) p (Over.forget X')) :
    (representing_object_unique p j j').hom =
      eqToHom (Functor.congr_obj (show (j'.inv.functor ⋙ j.hom.functor) ⋙ Over.forget X =
          Over.forget X' by rw [Functor.assoc, j.hom.w, j'.inv.w]) (Over.mk (𝟙 X'))).symm ≫
        ((j'.inv.functor ⋙ j.hom.functor).obj (Over.mk (𝟙 X'))).hom := by
  unfold representing_object_unique
  simp only [Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom, Over.forget_map]
  congr 1
  have h := Over.w ((Over.mkIdTerminal.isTerminalObj
    ((EquivalenceOver.toEquivalence j').symm.trans (EquivalenceOver.toEquivalence j)).functor
      _).uniqueUpToIso Over.mkIdTerminal).hom
  exact (Category.comp_id _).symm.trans h

/-- The structure morphism of `j s` is that of `j' s` followed by the structure morphism of
`j (j'⁻¹ (X', 𝟙 X'))`, up to the identifications of underlying objects (all are `p s`
or `X'`). -/
lemma equivalenceOver_obj_hom_eq (p : 𝒮 ⥤ 𝒞) {X X' : 𝒞}
    (j : EquivalenceOver (𝒞 := 𝒞) p (Over.forget X))
    (j' : EquivalenceOver (𝒞 := 𝒞) p (Over.forget X')) (s : 𝒮) :
    eqToHom ((Functor.congr_obj j'.hom.w s).trans (Functor.congr_obj j.hom.w s).symm) ≫
        (j.hom.functor.obj s).hom =
      (j'.hom.functor.obj s).hom ≫
        eqToHom (Functor.congr_obj (show (j'.inv.functor ⋙ j.hom.functor) ⋙ Over.forget X =
          Over.forget X' by rw [Functor.assoc, j.hom.w, j'.inv.w]) (Over.mk (𝟙 X'))).symm ≫
        ((j'.inv.functor ⋙ j.hom.functor).obj (Over.mk (𝟙 X'))).hom := by
  have hu := congrArg (fun n => n.app s) j'.unit_over
  simp only [Functor.whiskerRight_app, eqToHom_app] at hu
  have hF : (j'.inv.functor ⋙ j.hom.functor) ⋙ Over.forget X = Over.forget X' := by
    rw [Functor.assoc, j.hom.w, j'.inv.w]
  have hjm := Functor.congr_hom j.hom.w (j'.unitIso.hom.app s)
  simp only [Functor.comp_map, Over.forget_map] at hjm
  have hw := Over.w (j.hom.functor.map (j'.unitIso.hom.app s))
  have hF' := over_hom_eq_of_comp_forget_eq _ hF (j'.hom.functor.obj s)
  simp only [Functor.comp_obj, Functor.id_obj] at hw hF'
  rw [← hw, hjm, hu, hF']
  simp

/-- The structure morphism of `j s` is that of `j' s` followed by
`representing_object_unique p j j'`, up to the identification of the underlying objects
(both are `p s`). -/
lemma representingPair_hom_eq (p : 𝒮 ⥤ 𝒞) {X X' : 𝒞} (j : RepresentableBy p X)
    (j' : RepresentableBy p X') (s : 𝒮) :
    eqToHom ((Functor.congr_obj j'.hom.w s).trans (Functor.congr_obj j.hom.w s).symm) ≫
        (j.hom.functor.obj s).hom =
      (j'.hom.functor.obj s).hom ≫ (representing_object_unique p j j').hom :=
  (equivalenceOver_obj_hom_eq p j j' s).trans (by rw [representing_object_unique_hom p j j'])

/-- The 2-isomorphism of Stacks 02Y3 (2): `j` is isomorphic to `j'` followed by the slice
functor `Over.map φ.hom : 𝒞/X' ⥤ 𝒞/X`, where `φ = representing_object_unique p j j'`. Its
components are identities on underlying objects; see `representingPairIso_over` for the
statement that it is a 2-isomorphism over `𝒞`. -/
noncomputable def representingPairIso (p : 𝒮 ⥤ 𝒞) {X X' : 𝒞} (j : RepresentableBy p X)
    (j' : RepresentableBy p X') :
    j'.hom.functor ⋙ Over.map (representing_object_unique p j j').hom ≅ j.hom.functor :=
  NatIso.ofComponents
    (fun s => Over.isoMk
      (eqToIso ((Functor.congr_obj j'.hom.w s).trans (Functor.congr_obj j.hom.w s).symm))
      (by simpa using representingPair_hom_eq p j j' s))
    (fun {s s'} g => by
      apply Over.OverMorphism.ext
      have h1 := Functor.congr_hom j'.hom.w g
      have h2 := Functor.congr_hom j.hom.w g
      simp only [Functor.comp_map, Over.forget_map] at h1 h2
      simp [h1, h2])

/-- The 2-isomorphism `representingPairIso p j j'` lies over `𝒞`: whiskering it with the
structure functor `Over.forget X` gives the identity 2-cell. -/
lemma representingPairIso_over (p : 𝒮 ⥤ 𝒞) {X X' : 𝒞} (j : RepresentableBy p X)
    (j' : RepresentableBy p X') :
    Functor.whiskerRight (representingPairIso p j j').hom (Over.forget X) =
      eqToHom (by rw [Functor.assoc, Over.mapForget_eq, j'.hom.w, j.hom.w]) := by
  ext s
  simp [representingPairIso, eqToHom_app]

/-- **Stacks 02Y3** (part 2). If a category `p : 𝒮 ⥤ 𝒞` is representable, the pair `(X, j)`,
with `j : 𝒮 → 𝒞/X` an equivalence over `𝒞`, is uniquely determined up to isomorphism: for
two such pairs `(X, j)` and `(X', j')` there is an isomorphism `φ : X' ≅ X` in `𝒞` and a
2-isomorphism `α : (𝒞/φ) ∘ j' ≅ j` over `𝒞`, where `𝒞/φ = Over.map φ.hom : 𝒞/X' ⥤ 𝒞/X`;
"over `𝒞`" means that `α` whiskered with `Over.forget X` is the identity 2-cell. -/
@[stacks 02Y3 "(2); stated for any category over C, Stacks' case is p fibred in groupoids"]
theorem representing_pair_unique (p : 𝒮 ⥤ 𝒞) {X X' : 𝒞} (j : RepresentableBy p X)
    (j' : RepresentableBy p X') :
    ∃ φ : X' ≅ X, ∃ α : j'.hom.functor ⋙ Over.map φ.hom ≅ j.hom.functor,
      Functor.whiskerRight α.hom (Over.forget X) =
        eqToHom (by rw [Functor.assoc, Over.mapForget_eq, j'.hom.w, j.hom.w]) :=
  ⟨representing_object_unique p j j', representingPairIso p j j', representingPairIso_over p j j'⟩

end StacksRepresentableCFG
