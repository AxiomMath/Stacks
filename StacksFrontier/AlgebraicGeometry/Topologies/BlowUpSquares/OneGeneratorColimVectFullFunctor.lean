module

public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.OneGeneratorColimVectComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.OneGeneratorColimVectFull

/-!
# The comparison functor of Stacks Tag 0EXC is full

Let `p` be a prime, let `A` be a ring in characteristic `p`, let `f ∈ A` and let `J ⊆ A` be an
ideal, so that the spectra of

```
A ⧸ (J + fA) <--- A ⧸ J
      ^             ^
      |             |
   A ⧸ fA   <---    A
```

form the almost blowup square of More on Flatness, Example 0EVG. This file proves that
**the comparison functor of Stacks Tag 0EXC**

`colim_F Vect(X) ⟶ colim_F Vect(Z) ×_{colim_F Vect(E)} colim_F Vect(X')`

is **full**, the other half of the full faithfulness of Stacks Tag 0EXC; faithfulness is
`AlgebraicGeometry.colimVectComparison_faithful`.

## Main results

* `AlgebraicGeometry.colimVectComparison_full`: **the comparison functor of Stacks Tag 0EXC is
  full** for the one-generator almost blowup square of Example 0EVG.
* `AlgebraicGeometry.squareColimVectIso_hom_app`: the comparison of the two composite transition
  functors around the square, at an object `(ℰ, n)`, is the stage-`n` functor applied to the
  inverse of `AlgebraicGeometry.OneGeneratorSquare.squareVectIso` at `ℰ`.
* `AlgebraicGeometry.OneGeneratorSquare.squareVectIso_symm_compat`: the inverse of
  `AlgebraicGeometry.OneGeneratorSquare.squareVectIso` is compatible with the Frobenius
  comparisons on the two legs of the square.
* `CategoryTheory.EndoColim.exists_untransportHom_naturality`: **the Hom-level content of
  fullness.** If two morphisms presented at a common level over a common stage are identified in
  the colimit category by an isomorphism `c : Φ ≅ Φ'` of the two inducing functors, then their
  unconjugated forms are identified by `c` on the nose, after a raise.
* `CategoryTheory.EndoColim.full_of_surjective_equalStage`: a functor out of `colim_F C` is full
  as soon as it is surjective on the Hom-sets between objects presented at one and the same
  stage.

## References

* [Stacks Project, Tag 0EVG](https://stacks.math.columbia.edu/tag/0EVG)
* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXC](https://stacks.math.columbia.edu/tag/0EXC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe v v₂ u u₂ u₃

namespace CategoryTheory

/-! ### Raising an iterate of a morphism of `C` -/

/-- **Raising an iterate of a morphism of `C` is a higher iterate of it**, with no transport of
exponents. -/
lemma endoRaise_endoIter_map_self {C : Type u} [Category.{v} C] (F : C ⥤ C) {E G : C} (g : E ⟶ G)
    (m : ℕ) : ∀ j : ℕ, endoRaise ((F.endoIter m).map g) j = (F.endoIter (m + j)).map g
  | 0 => rfl
  | j + 1 => by
      change F.map (endoRaise ((F.endoIter m).map g) j) = _
      rw [endoRaise_endoIter_map_self F g m j]
      rfl

/-! ### The component of a triple composite of isomorphisms of functors -/

/-- **The component of a composite of three isomorphisms of functors, the last one reversed.** -/
lemma iso_trans_trans_symm_hom_app {C : Type u} [Category.{v} C] {D : Type u₂}
    [Category.{v₂} D] {P Q R S : C ⥤ D} (α : P ≅ Q) (β : Q ≅ R) (γ : S ≅ R) (X : C) :
    (α ≪≫ β ≪≫ γ.symm).hom.app X = α.hom.app X ≫ β.hom.app X ≫ γ.inv.app X := rfl

/-! ### Surjectivity on a Hom-set transports along isomorphisms -/

/-- **Surjectivity of a functor's action on a Hom-set transports along isomorphisms** of the
source and of the target. -/
theorem Functor.surjective_map_of_isos {A : Type u₂} [Category.{v} A] {B : Type u₃}
    [Category.{v₂} B] (K : A ⥤ B) {a b x y : A} (ι : a ≅ x) (κ : b ≅ y)
    (h : Function.Surjective fun m : a ⟶ b ↦ K.map m) :
    Function.Surjective fun n : x ⟶ y ↦ K.map n := by
  have key : (fun n : x ⟶ y ↦ K.map n) =
      Iso.homCongr (K.mapIso ι) (K.mapIso κ) ∘ (fun m : a ⟶ b ↦ K.map m) ∘
        (Iso.homCongr ι κ).symm := by
    funext n
    simp [Iso.homCongr, Functor.map_comp]
  rw [key]
  exact (Iso.homCongr (K.mapIso ι) (K.mapIso κ)).surjective.comp
    (h.comp (Iso.homCongr ι κ).symm.surjective)

namespace EndoColim

/-! ### Fullness from the Hom-sets at a common stage -/

/-- **A functor out of `colim_F C` which is surjective on the Hom-sets between objects presented
at one and the same stage is full.** -/
theorem full_of_surjective_equalStage {C : Type u} [Category.{v} C] {D : Type u₂}
    [Category.{v₂} D] {F : C ⥤ C} (K : EndoColim F ⥤ D)
    (h : ∀ (n : ℕ) (E G : C),
      Function.Surjective fun u : (⟨E, n⟩ : EndoColim F) ⟶ ⟨G, n⟩ ↦ K.map u) :
    K.Full where
  map_surjective {A B} := by
    obtain ⟨E, n⟩ := A
    obtain ⟨G, m⟩ := B
    exact Functor.surjective_map_of_isos K (objShiftIso F n m E)
      (stageCastIso F ((F.endoIter n).obj G) (Nat.add_comm n m) ≪≫ objShiftIso F m n G)
      (h (n + m) ((F.endoIter m).obj E) ((F.endoIter n).obj G))

/-! ### The stage functor on a triple composite -/

/-- **The stage functor applied to a composite of three morphisms of `C`.** -/
lemma stageHomOf_comp₃ {C : Type u} [Category.{v} C] (F : C ⥤ C) (n : ℕ) {E G H K : C}
    (a : E ⟶ G) (b : G ⟶ H) (c : H ⟶ K) {d : E ⟶ K} (hd : a ≫ b ≫ c = d) :
    stageHomOf F n a ≫ stageHomOf F n b ≫ stageHomOf F n c = stageHomOf F n d := by
  rw [← stageHomOf_comp, ← stageHomOf_comp, hd]

/-! ### Closure properties of the compatibility of an isomorphism of the inducing functor -/

section Congr

variable {C : Type u} [Category.{v} C] {C' : Type u₂} [Category.{v} C'] (F : C ⥤ C)
  (F' : C' ⥤ C')

/-- **An isomorphism of the inducing functor whose components are compatible with the two
comparisons is compatible with them.** This is the converse of
`CategoryTheory.EndoColim.congr_hom_app`. -/
lemma congr_of_hom_app (Φ Φ' : C ⥤ C') (α : F ⋙ Φ ≅ Φ ⋙ F') (α' : F ⋙ Φ' ≅ Φ' ⋙ F')
    (c : Φ ≅ Φ')
    (h : ∀ E : C, c.hom.app (F.obj E) ≫ α'.hom.app E = α.hom.app E ≫ F'.map (c.hom.app E)) :
    Functor.isoWhiskerLeft F c ≪≫ α' = α ≪≫ Functor.isoWhiskerRight c F' :=
  Iso.ext (NatTrans.ext (funext fun E ↦ by simpa using h E))

/-- **The inverse of a compatible isomorphism of the inducing functor is compatible.** -/
lemma congr_symm (Φ Φ' : C ⥤ C') (α : F ⋙ Φ ≅ Φ ⋙ F') (α' : F ⋙ Φ' ≅ Φ' ⋙ F') (c : Φ ≅ Φ')
    (hc : Functor.isoWhiskerLeft F c ≪≫ α' = α ≪≫ Functor.isoWhiskerRight c F') :
    Functor.isoWhiskerLeft F c.symm ≪≫ α = α' ≪≫ Functor.isoWhiskerRight c.symm F' := by
  refine congr_of_hom_app F F' Φ' Φ α' α c.symm fun E ↦ ?_
  have h := congr_hom_app F F' Φ Φ' α α' c hc E
  have key : c.hom.app (F.obj E) ≫ c.symm.hom.app (F.obj E) ≫ α.hom.app E =
      c.hom.app (F.obj E) ≫ α'.hom.app E ≫ F'.map (c.symm.hom.app E) := by
    rw [Iso.symm_hom, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp,
      reassoc_of% h, ← F'.map_comp, Iso.hom_inv_id_app, F'.map_id, Category.comp_id]
  exact (cancel_epi (c.hom.app (F.obj E))).mp key

/-- **A composite of compatible isomorphisms of the inducing functor is compatible.** -/
lemma congr_trans (Φ Ξ Φ' : C ⥤ C') (α : F ⋙ Φ ≅ Φ ⋙ F') (α₂ : F ⋙ Ξ ≅ Ξ ⋙ F')
    (α' : F ⋙ Φ' ≅ Φ' ⋙ F') (c₁ : Φ ≅ Ξ) (c₂ : Ξ ≅ Φ')
    (hc₁ : Functor.isoWhiskerLeft F c₁ ≪≫ α₂ = α ≪≫ Functor.isoWhiskerRight c₁ F')
    (hc₂ : Functor.isoWhiskerLeft F c₂ ≪≫ α' = α₂ ≪≫ Functor.isoWhiskerRight c₂ F') :
    Functor.isoWhiskerLeft F (c₁ ≪≫ c₂) ≪≫ α' =
      α ≪≫ Functor.isoWhiskerRight (c₁ ≪≫ c₂) F' := by
  refine congr_of_hom_app F F' Φ Φ' α α' (c₁ ≪≫ c₂) fun E ↦ ?_
  have h₁ := congr_hom_app F F' Φ Ξ α α₂ c₁ hc₁ E
  have h₂ := congr_hom_app F F' Ξ Φ' α₂ α' c₂ hc₂ E
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [h₂, reassoc_of% h₁]

end Congr

/-! ### The unconjugated form of a morphism, for a composite and under a transport -/

section Untransport

variable {C : Type u} [Category.{v} C] {C' : Type u₂} [Category.{v} C'] {C'' : Type u₃}
  [Category.{v} C'']

/-- **The unconjugated form of a morphism for a composite of two functors is the image under the
second of the unconjugated form for the first.** -/
lemma map_untransportHom (F : C ⥤ C) (F' : C' ⥤ C') (F'' : C'' ⥤ C'') (Φ : C ⥤ C')
    (Ψ : C' ⥤ C'') (α : F ⋙ Φ ≅ Φ ⋙ F') (β : F' ⋙ Ψ ≅ Ψ ⋙ F'') (a : ℕ) {E G : C}
    (x : (F'.endoIter a).obj (Φ.obj E) ⟶ (F'.endoIter a).obj (Φ.obj G)) :
    untransportHom F F'' (Φ ⋙ Ψ) (compComm F F' F'' Φ Ψ α β) a
        (transportHom F' F'' Ψ β a x) =
      Ψ.map (untransportHom F F' Φ α a x) := by
  rw [untransportHom, untransportHom, transportHom, squareIter_compComm_inv,
    squareIter_compComm, Ψ.map_comp, Ψ.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- **A transport of exponents passes through the morphism between iterates which a morphism
induces.** -/
lemma endoHomCast_transportHom' (F : C ⥤ C) (F' : C' ⥤ C') (Φ : C ⥤ C') (α : F ⋙ Φ ≅ Φ ⋙ F')
    {a a' : ℕ} (h : a = a') {E G : C}
    (g : (F.endoIter a).obj E ⟶ (F.endoIter a).obj G) :
    endoHomCast h h (transportHom F F' Φ α a g) =
      transportHom F F' Φ α a' (endoHomCast h h g) := by
  subst h; rfl

/-- **The unconjugated form, for a composite of two functors, of a raised and transported
morphism induced by the second functor.** -/
lemma untransportHom_endoHomCast_endoRaise_transportHom (F : C ⥤ C) (F' : C' ⥤ C')
    (F'' : C'' ⥤ C'') (Φ : C ⥤ C') (Ψ : C' ⥤ C'') (α : F ⋙ Φ ≅ Φ ⋙ F')
    (β : F' ⋙ Ψ ≅ Ψ ⋙ F'') {a N j : ℕ} (hN : a + j = N) {E G : C}
    (g : (F'.endoIter a).obj (Φ.obj E) ⟶ (F'.endoIter a).obj (Φ.obj G)) :
    untransportHom F F'' (Φ ⋙ Ψ) (compComm F F' F'' Φ Ψ α β) N
        (endoHomCast hN hN (endoRaise (transportHom F' F'' Ψ β a g) j)) =
      Ψ.map (untransportHom F F' Φ α N (endoHomCast hN hN (endoRaise g j))) := by
  rw [endoRaise_transportHom, endoHomCast_transportHom', map_untransportHom]

end Untransport

/-! ### The Hom-level content of fullness -/

section Naturality

variable {C : Type u} [Category.{v} C] {C' : Type u₂} [Category.{v} C'] (F : C ⥤ C)
  (F' : C' ⥤ C') (Φ Φ' : C ⥤ C') (α : F ⋙ Φ ≅ Φ ⋙ F') (α' : F ⋙ Φ' ≅ Φ' ⋙ F') (c : Φ ≅ Φ')

/-- **The Hom-level content of fullness.** Let `c : Φ ≅ Φ'` be an isomorphism of two functors
each commuting with the endofunctors, and let two morphisms of `C'` between the iterates of `F'`
at the images of `E` and `G` present, at a common level `k` over a common stage `n`, two
morphisms of `colim_{F'} C'` which `c` identifies. Then the unconjugated forms
`CategoryTheory.EndoColim.untransportHom` of the two presenting morphisms are identified by `c`
on the nose, after a raise. -/
theorem exists_untransportHom_naturality
    (hc : Functor.isoWhiskerLeft F c ≪≫ α' = α ≪≫ Functor.isoWhiskerRight c F')
    (n k : ℕ) {E G : C}
    (x : (F'.endoIter (n + k)).obj (Φ.obj E) ⟶ (F'.endoIter (n + k)).obj (Φ.obj G))
    (y : (F'.endoIter (n + k)).obj (Φ'.obj E) ⟶ (F'.endoIter (n + k)).obj (Φ'.obj G))
    (hw : (Hom.of k x : (⟨Φ.obj E, n⟩ : EndoColim F') ⟶ ⟨Φ.obj G, n⟩) ≫
          stageHomOf F' n (c.hom.app G) =
        stageHomOf F' n (c.hom.app E) ≫
          (Hom.of k y : (⟨Φ'.obj E, n⟩ : EndoColim F') ⟶ ⟨Φ'.obj G, n⟩)) :
    ∃ j : ℕ, ∀ (N : ℕ) (hN : k + j = N),
      untransportHom F F' Φ α (n + N)
            (endoHomCast (by omega) (by omega) (endoRaise x j)) ≫
          c.hom.app ((F.endoIter (n + N)).obj G) =
        c.hom.app ((F.endoIter (n + N)).obj E) ≫
          untransportHom F F' Φ' α' (n + N)
            (endoHomCast (by omega) (by omega) (endoRaise y j)) := by
  rw [Hom.of_comp_stageHomOf F' n n k x (c.hom.app G),
    stageHomOf_comp_Hom_of F' n n k (c.hom.app E) y] at hw
  obtain ⟨j, i, hji, he⟩ := (Hom.of_eq_of_iff _ _).mp hw
  have hji' : k + j = k + i := hji
  obtain rfl : j = i := by omega
  have he' : endoRaise (x ≫ (F'.endoIter (n + k)).map (c.hom.app G)) j =
      endoRaise ((F'.endoIter (n + k)).map (c.hom.app E) ≫ y) j :=
    endoHomCast_injective _ _ he
  rw [endoRaise_comp, endoRaise_comp, endoRaise_endoIter_map_self,
    endoRaise_endoIter_map_self] at he'
  refine ⟨j, fun N _ ↦ ?_⟩
  have key : ∀ (a : ℕ) (ha : n + k + j = a),
      untransportHom F F' Φ α a (endoHomCast ha ha (endoRaise x j)) ≫
            c.hom.app ((F.endoIter a).obj G) =
          c.hom.app ((F.endoIter a).obj E) ≫
            untransportHom F F' Φ' α' a (endoHomCast ha ha (endoRaise y j)) := by
    rintro a rfl
    rw [endoHomCast_rfl, endoHomCast_rfl, untransportHom, untransportHom]
    have hcE := squareIter_congr F F' Φ Φ' α α' c hc (n + k + j) E
    have hcG := squareIter_congr F F' Φ Φ' α α' c hc (n + k + j) G
    have hE : (squareIter F F' Φ α (n + k + j) E).inv ≫
          (F'.endoIter (n + k + j)).map (c.hom.app E) ≫
            (squareIter F F' Φ' α' (n + k + j) E).hom =
        c.hom.app ((F.endoIter (n + k + j)).obj E) := by
      rw [hcE, Iso.inv_hom_id_assoc]
    rw [← hE]
    simp only [Category.assoc]
    rw [← hcG, reassoc_of% he']
    simp
  exact key (n + N) (by omega)

end Naturality

end EndoColim

end CategoryTheory

namespace AlgebraicGeometry

/-! ### Restriction along equal morphisms, and the Frobenius comparison -/

/-- **Comparing the restrictions of vector bundles along two equal morphisms gives the identity
when the two morphisms are the same term.** -/
lemma vectPullbackCongr_refl_hom_app {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Vect) :
    (Scheme.Vect.pullbackCongr (rfl : g = g)).hom.app M = 𝟙 _ :=
  ObjectProperty.hom_ext _ (by simp [Scheme.Modules.pullbackCongr])

/-- **The comparison of the restrictions along two equal morphisms is compatible with the
Frobenius comparisons.** -/
lemma vectPullbackCongr_frobeniusVectPullbackIso_compat (p : ℕ) [Fact p.Prime] {X Y : Scheme.{u}}
    (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) {g h : X ⟶ Y} (e : g = h) :
    Functor.isoWhiskerLeft (frobeniusPullback Y p hY) (Scheme.Vect.pullbackCongr e) ≪≫
        frobeniusVectPullbackIso h p hX hY =
      frobeniusVectPullbackIso g p hX hY ≪≫
        Functor.isoWhiskerRight (Scheme.Vect.pullbackCongr e) (frobeniusPullback X p hX) := by
  subst e
  refine EndoColim.congr_of_hom_app _ _ _ _ _ _ _ fun M ↦ ?_
  simp [vectPullbackCongr_refl_hom_app]

/-- **The inverse of the canonical comparison attached to a commuting square of schemes, as a
composite of pseudofunctoriality comparisons.** -/
lemma vectPullbackSquareIso_symm_eq {W X Y Z : Scheme.{u}} {a : W ⟶ Y} {b : Y ⟶ X} {c : W ⟶ Z}
    {d : Z ⟶ X} (h : a ≫ b = c ≫ d) :
    (vectPullbackSquareIso h).symm =
      Scheme.Vect.pullbackComp c d ≪≫ (Scheme.Vect.pullbackCongr h).symm ≪≫
        (Scheme.Vect.pullbackComp a b).symm :=
  Iso.ext (NatTrans.ext (funext fun M ↦
    ObjectProperty.hom_ext _ (by simp [modulesPullbackSquareIso])))

/-- **The inverse of the canonical comparison attached to a commuting square of schemes, at an
object.** This is `AlgebraicGeometry.vectPullbackSquareIso_symm_eq` read at a vector bundle. -/
lemma vectPullbackSquareIso_inv_app_eq {W X Y Z : Scheme.{u}} {a : W ⟶ Y} {b : Y ⟶ X}
    {c : W ⟶ Z} {d : Z ⟶ X} (h : a ≫ b = c ≫ d) (M : X.Vect) :
    (vectPullbackSquareIso h).inv.app M =
      (Scheme.Vect.pullbackComp c d).hom.app M ≫
        (Scheme.Vect.pullbackCongr h).inv.app M ≫
          (Scheme.Vect.pullbackComp a b).inv.app M :=
  by rw [← Iso.symm_hom, vectPullbackSquareIso_symm_eq h, iso_trans_trans_symm_hom_app]; rfl

/-- **The inverse comparison of
`AlgebraicGeometry.OneGeneratorSquare.colimVectPullbackComp` at the object `(ℰ, n)`** is the
stage-`n` functor applied to the inverse comparison of the two restrictions of `ℰ`. -/
@[simp]
lemma OneGeneratorSquare.colimVectPullbackComp_inv_app (p : ℕ) [Fact p.Prime]
    {X Y Z : Scheme.{u}} (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (hZ : IsInCharacteristic Z p) (g : X ⟶ Y) (h : Y ⟶ Z) (E : Z.Vect) (n : ℕ) :
    (OneGeneratorSquare.colimVectPullbackComp p hX hY hZ g h).inv.app ⟨E, n⟩ =
      EndoColim.stageHomOf (frobeniusPullback X p hX) n
        ((Scheme.Vect.pullbackComp g h).inv.app E) :=
  Category.comp_id _

/-! ### The remaining data of the one-generator square -/

namespace OneGeneratorSquare

variable (A : Type u) [CommRing A] (f : A) (J : Ideal A) (p : ℕ) [Fact p.Prime]
  (hp : (p : A) = 0)

/-- Frobenius pullback of vector bundles on the exceptional corner `Spec (A ⧸ (J + fA))` of the
square. -/
abbrev frobExc : (Spec (CommRingCat.of (A ⧸ (J ⊔ Ideal.span {f})))).Vect ⥤
    (Spec (CommRingCat.of (A ⧸ (J ⊔ Ideal.span {f})))).Vect :=
  frobeniusPullback (Spec (CommRingCat.of (A ⧸ (J ⊔ Ideal.span {f})))) p (charExc A f J p hp)

/-- Restriction of vector bundles along the closed immersion of the exceptional corner into the
centre, `Spec (A ⧸ (J + fA)) ⟶ Spec (A ⧸ fA)`. -/
abbrev vectCtrExc : (Spec (CommRingCat.of (A ⧸ Ideal.span {f}))).Vect ⥤
    (Spec (CommRingCat.of (A ⧸ (J ⊔ Ideal.span {f})))).Vect :=
  Scheme.Vect.pullback (Spec.map (ctrToExc A f J))

/-- Restriction of vector bundles along the closed immersion of the exceptional corner into the
modification, `Spec (A ⧸ (J + fA)) ⟶ Spec (A ⧸ J)`. -/
abbrev vectModExc : (Spec (CommRingCat.of (A ⧸ J))).Vect ⥤
    (Spec (CommRingCat.of (A ⧸ (J ⊔ Ideal.span {f})))).Vect :=
  Scheme.Vect.pullback (Spec.map (modToExc A f J))

/-- Restriction of vector bundles from `Spec A` to the exceptional corner through the centre. -/
abbrev vectViaCtr : (Spec (CommRingCat.of A)).Vect ⥤
    (Spec (CommRingCat.of (A ⧸ (J ⊔ Ideal.span {f})))).Vect :=
  vectCtr A f ⋙ vectCtrExc A f J

/-- Restriction of vector bundles from `Spec A` to the exceptional corner through the
modification. -/
abbrev vectViaMod : (Spec (CommRingCat.of A)).Vect ⥤
    (Spec (CommRingCat.of (A ⧸ (J ⊔ Ideal.span {f})))).Vect :=
  vectMod A J ⋙ vectModExc A f J

/-- The comparison of `AlgebraicGeometry.frobeniusVectPullbackIso` for restriction from the
centre to the exceptional corner. -/
abbrev frobVectIsoCtrExc :
    frobCtr A f p hp ⋙ vectCtrExc A f J ≅ vectCtrExc A f J ⋙ frobExc A f J p hp :=
  frobeniusVectPullbackIso (Spec.map (ctrToExc A f J)) p (charExc A f J p hp) (charCtr A f p hp)

/-- The comparison of `AlgebraicGeometry.frobeniusVectPullbackIso` for restriction from the
modification to the exceptional corner. -/
abbrev frobVectIsoModExc :
    frobMod A J p hp ⋙ vectModExc A f J ≅ vectModExc A f J ⋙ frobExc A f J p hp :=
  frobeniusVectPullbackIso (Spec.map (modToExc A f J)) p (charExc A f J p hp) (charMod A J p hp)

/-- The comparison of Frobenius pullback with the double restriction to the exceptional corner
through the centre, as the comparison `CategoryTheory.EndoColim.compComm` of the two steps. -/
abbrev frobVectIsoViaCtr :
    frobBase A p hp ⋙ vectViaCtr A f J ≅ vectViaCtr A f J ⋙ frobExc A f J p hp :=
  EndoColim.compComm (frobBase A p hp) (frobCtr A f p hp) (frobExc A f J p hp) (vectCtr A f)
    (vectCtrExc A f J) (frobVectIsoCtr A f p hp) (frobVectIsoCtrExc A f J p hp)

/-- The comparison of Frobenius pullback with the double restriction to the exceptional corner
through the modification, as the comparison `CategoryTheory.EndoColim.compComm` of the two
steps. -/
abbrev frobVectIsoViaMod :
    frobBase A p hp ⋙ vectViaMod A f J ≅ vectViaMod A f J ⋙ frobExc A f J p hp :=
  EndoColim.compComm (frobBase A p hp) (frobMod A J p hp) (frobExc A f J p hp) (vectMod A J)
    (vectModExc A f J) (frobVectIsoMod A J p hp) (frobVectIsoModExc A f J p hp)

/-- **The comparison of the two double restrictions to the exceptional corner is compatible with
the Frobenius comparisons.** -/
lemma squareVectIso_symm_compat :
    Functor.isoWhiskerLeft (frobBase A p hp) (squareVectIso A f J).symm ≪≫
        frobVectIsoViaMod A f J p hp =
      frobVectIsoViaCtr A f J p hp ≪≫
        Functor.isoWhiskerRight (squareVectIso A f J).symm (frobExc A f J p hp) := by
  have hdec : (squareVectIso A f J).symm =
      Scheme.Vect.pullbackComp (Spec.map (ctrToExc A f J)) (Spec.map (toCtr A f)) ≪≫
        (Scheme.Vect.pullbackCongr (specMap_square A f J)).symm ≪≫
          (Scheme.Vect.pullbackComp (Spec.map (modToExc A f J)) (Spec.map (toMod A J))).symm :=
    vectPullbackSquareIso_symm_eq (specMap_square A f J)
  rw [hdec]
  refine EndoColim.congr_trans (frobBase A p hp) (frobExc A f J p hp) _ _ _ _ _ _ _ _
    (frobeniusVectPullbackIso_compComm p (charExc A f J p hp) (charCtr A f p hp)
      (charBase A p hp) (Spec.map (ctrToExc A f J)) (Spec.map (toCtr A f))) ?_
  refine EndoColim.congr_trans (frobBase A p hp) (frobExc A f J p hp) _ _ _ _ _ _ _ _
    (EndoColim.congr_symm (frobBase A p hp) (frobExc A f J p hp) _ _ _ _ _
      (vectPullbackCongr_frobeniusVectPullbackIso_compat p (charExc A f J p hp)
        (charBase A p hp) (specMap_square A f J))) ?_
  exact EndoColim.congr_symm (frobBase A p hp) (frobExc A f J p hp) _ _ _ _ _
    (frobeniusVectPullbackIso_compComm p (charExc A f J p hp) (charMod A J p hp)
      (charBase A p hp) (Spec.map (modToExc A f J)) (Spec.map (toMod A J)))

end OneGeneratorSquare

/-! ### The two comparisons for equal restrictions, at an object -/

/-- **Comparing the restrictions of vector bundles along two equal morphisms gives the identity
when the two morphisms are the same term**, on the inverse half. -/
lemma vectPullbackCongr_refl_inv_app {X Y : Scheme.{u}} (g : X ⟶ Y) (M : Y.Vect) :
    (Scheme.Vect.pullbackCongr (rfl : g = g)).inv.app M = 𝟙 _ :=
  ObjectProperty.hom_ext _ (by simp [Scheme.Modules.pullbackCongr])

/-- **The comparison of the restrictions along two equal morphisms, read on the colimit
categories, is the stage functor applied to the comparison on vector bundles.** -/
lemma OneGeneratorSquare.colimVectPullback_eqToIso_hom_app (p : ℕ) [Fact p.Prime]
    {X Y : Scheme.{u}} (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    {g h : X ⟶ Y} (e : g = h)
    (q : OneGeneratorSquare.colimVectPullback p hX hY h =
      OneGeneratorSquare.colimVectPullback p hX hY g) (E : Y.Vect) (n : ℕ) :
    (eqToIso q).hom.app ⟨E, n⟩ =
      EndoColim.stageHomOf (frobeniusPullback X p hX) n
        ((Scheme.Vect.pullbackCongr e).inv.app E) := by
  subst e
  obtain rfl : q = rfl := rfl
  have h₁ : (eqToIso (rfl : OneGeneratorSquare.colimVectPullback p hX hY g =
          OneGeneratorSquare.colimVectPullback p hX hY g)).hom.app
      (⟨E, n⟩ : frobeniusColimitVectModel Y p hY) = 𝟙 _ := rfl
  rw [h₁, vectPullbackCongr_refl_inv_app, EndoColim.stageHomOf,
    CategoryTheory.Functor.map_id]
  exact (EndoColim.Hom.of_id _ 0).symm

/-- **The middle factor of the comparison for a commuting square of schemes, at an object.** -/
lemma colimVectSquareIso_hom_app_mid {W X Y Z : Scheme.{u}} (p : ℕ) [Fact p.Prime]
    (hW : IsInCharacteristic W p) (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    {a : W ⟶ Y} {b : Y ⟶ X} {c : W ⟶ Z} {d : Z ⟶ X} (h : a ≫ b = c ≫ d)
    (q : OneGeneratorSquare.colimVectPullback p hW hX (c ≫ d) =
      OneGeneratorSquare.colimVectPullback p hW hX (a ≫ b)) (E : X.Vect) (n : ℕ) :
    (eqToIso q).hom.app ⟨E, n⟩ ≫
        (OneGeneratorSquare.colimVectPullbackComp p hW hY hX a b).inv.app ⟨E, n⟩ =
      EndoColim.stageHomOf (frobeniusPullback W p hW) n
          ((Scheme.Vect.pullbackCongr h).inv.app E) ≫
        (OneGeneratorSquare.colimVectPullbackComp p hW hY hX a b).inv.app ⟨E, n⟩ :=
  eq_whisker (OneGeneratorSquare.colimVectPullback_eqToIso_hom_app p hW hX h q E n) _

/-- **The last factor of the comparison for a commuting square of schemes, at an object.** -/
lemma colimVectSquareIso_hom_app_last {W X Y Z : Scheme.{u}} (p : ℕ) [Fact p.Prime]
    (hW : IsInCharacteristic W p) (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    {a : W ⟶ Y} {b : Y ⟶ X} {c : W ⟶ Z} {d : Z ⟶ X} (h : a ≫ b = c ≫ d) (E : X.Vect) (n : ℕ) :
    EndoColim.stageHomOf (frobeniusPullback W p hW) n
          ((Scheme.Vect.pullbackCongr h).inv.app E) ≫
        (OneGeneratorSquare.colimVectPullbackComp p hW hY hX a b).inv.app ⟨E, n⟩ =
      EndoColim.stageHomOf (frobeniusPullback W p hW) n
          ((Scheme.Vect.pullbackCongr h).inv.app E) ≫
        EndoColim.stageHomOf (frobeniusPullback W p hW) n
          ((Scheme.Vect.pullbackComp a b).inv.app E) :=
  whisker_eq _ (OneGeneratorSquare.colimVectPullbackComp_inv_app p hW hY hX a b E n)

/-- **The last two factors of the comparison for a commuting square of schemes, at an
object.** -/
lemma colimVectSquareIso_hom_app_tail {W X Y Z : Scheme.{u}} (p : ℕ) [Fact p.Prime]
    (hW : IsInCharacteristic W p) (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    {a : W ⟶ Y} {b : Y ⟶ X} {c : W ⟶ Z} {d : Z ⟶ X} (h : a ≫ b = c ≫ d)
    (q : OneGeneratorSquare.colimVectPullback p hW hX (c ≫ d) =
      OneGeneratorSquare.colimVectPullback p hW hX (a ≫ b)) (E : X.Vect) (n : ℕ) :
    (eqToIso q).hom.app ⟨E, n⟩ ≫
        (OneGeneratorSquare.colimVectPullbackComp p hW hY hX a b).inv.app ⟨E, n⟩ =
      EndoColim.stageHomOf (frobeniusPullback W p hW) n
          ((Scheme.Vect.pullbackCongr h).inv.app E) ≫
        EndoColim.stageHomOf (frobeniusPullback W p hW) n
          ((Scheme.Vect.pullbackComp a b).inv.app E) :=
  (colimVectSquareIso_hom_app_mid p hW hX hY h q E n).trans
    (colimVectSquareIso_hom_app_last p hW hX hY h E n)

/-- **The first factor of the comparison for a commuting square of schemes, at an object.** -/
lemma colimVectSquareIso_hom_app_head {W X Y Z : Scheme.{u}} (p : ℕ) [Fact p.Prime]
    (hW : IsInCharacteristic W p) (hX : IsInCharacteristic X p)
    (hZ : IsInCharacteristic Z p) {a : W ⟶ Y} {b : Y ⟶ X} {c : W ⟶ Z} {d : Z ⟶ X}
    (h : a ≫ b = c ≫ d) (E : X.Vect) (n : ℕ) :
    (OneGeneratorSquare.colimVectPullbackComp p hW hZ hX c d).hom.app ⟨E, n⟩ ≫
        (EndoColim.stageHomOf (frobeniusPullback W p hW) n
            ((Scheme.Vect.pullbackCongr h).inv.app E) ≫
          EndoColim.stageHomOf (frobeniusPullback W p hW) n
            ((Scheme.Vect.pullbackComp a b).inv.app E)) =
      EndoColim.stageHomOf (frobeniusPullback W p hW) n
            ((Scheme.Vect.pullbackComp c d).hom.app E) ≫
          EndoColim.stageHomOf (frobeniusPullback W p hW) n
            ((Scheme.Vect.pullbackCongr h).inv.app E) ≫
        EndoColim.stageHomOf (frobeniusPullback W p hW) n
          ((Scheme.Vect.pullbackComp a b).inv.app E) :=
  eq_whisker (OneGeneratorSquare.colimVectPullbackComp_hom_app p hW hZ hX c d E n) _

/-- **The three factors of the comparison for a commuting square of schemes, at an object.** -/
lemma colimVectSquareIso_hom_app_factors {W X Y Z : Scheme.{u}} (p : ℕ) [Fact p.Prime]
    (hW : IsInCharacteristic W p) (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (hZ : IsInCharacteristic Z p) {a : W ⟶ Y} {b : Y ⟶ X} {c : W ⟶ Z} {d : Z ⟶ X}
    (h : a ≫ b = c ≫ d)
    (q : OneGeneratorSquare.colimVectPullback p hW hX (c ≫ d) =
      OneGeneratorSquare.colimVectPullback p hW hX (a ≫ b)) (E : X.Vect) (n : ℕ) :
    (OneGeneratorSquare.colimVectPullbackComp p hW hZ hX c d).hom.app ⟨E, n⟩ ≫
          (eqToIso q).hom.app ⟨E, n⟩ ≫
        (OneGeneratorSquare.colimVectPullbackComp p hW hY hX a b).inv.app ⟨E, n⟩ =
      EndoColim.stageHomOf (frobeniusPullback W p hW) n
            ((Scheme.Vect.pullbackComp c d).hom.app E) ≫
          EndoColim.stageHomOf (frobeniusPullback W p hW) n
            ((Scheme.Vect.pullbackCongr h).inv.app E) ≫
        EndoColim.stageHomOf (frobeniusPullback W p hW) n
          ((Scheme.Vect.pullbackComp a b).inv.app E) :=
  (whisker_eq _ (colimVectSquareIso_hom_app_tail p hW hX hY h q E n)).trans
    (colimVectSquareIso_hom_app_head p hW hX hZ h E n)

/-- **The comparison of the two double restrictions along the legs of a commuting square of
schemes, read on the colimit categories, is the stage functor applied to the comparison on
vector bundles.** -/
lemma colimVectSquareIso_hom_app {W X Y Z : Scheme.{u}} (p : ℕ) [Fact p.Prime]
    (hW : IsInCharacteristic W p) (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p)
    (hZ : IsInCharacteristic Z p) {a : W ⟶ Y} {b : Y ⟶ X} {c : W ⟶ Z} {d : Z ⟶ X}
    (h : a ≫ b = c ≫ d)
    (q : OneGeneratorSquare.colimVectPullback p hW hX (c ≫ d) =
      OneGeneratorSquare.colimVectPullback p hW hX (a ≫ b)) (E : X.Vect) (n : ℕ) :
    (OneGeneratorSquare.colimVectPullbackComp p hW hZ hX c d ≪≫ eqToIso q ≪≫
          (OneGeneratorSquare.colimVectPullbackComp p hW hY hX a b).symm).hom.app ⟨E, n⟩ =
      EndoColim.stageHomOf (frobeniusPullback W p hW) n
        ((vectPullbackSquareIso h).inv.app E) :=
  ((iso_trans_trans_symm_hom_app _ _ _ _).trans
      (colimVectSquareIso_hom_app_factors p hW hX hY hZ h q E n)).trans
    (EndoColim.stageHomOf_comp₃ _ n _ _ _ (vectPullbackSquareIso_inv_app_eq h E).symm)

/-- **The comparison of the two composite transition functors of the square of Example 0EVG,
written out.** -/
lemma squareColimVectIso_eq (A : Type u) [CommRing A] (f : A) (J : Ideal A) (p : ℕ)
    [Fact p.Prime] (hp : (p : A) = 0) :
    squareColimVectIso A f J p hp =
      OneGeneratorSquare.colimVectPullbackComp p (OneGeneratorSquare.charExc A f J p hp)
          (OneGeneratorSquare.charCtr A f p hp) (OneGeneratorSquare.charBase A p hp)
          (Spec.map (OneGeneratorSquare.ctrToExc A f J))
          (Spec.map (OneGeneratorSquare.toCtr A f)) ≪≫
        eqToIso (congrArg
            (OneGeneratorSquare.colimVectPullback p (OneGeneratorSquare.charExc A f J p hp)
              (OneGeneratorSquare.charBase A p hp))
            (OneGeneratorSquare.specMap_square A f J).symm) ≪≫
          (OneGeneratorSquare.colimVectPullbackComp p (OneGeneratorSquare.charExc A f J p hp)
            (OneGeneratorSquare.charMod A J p hp) (OneGeneratorSquare.charBase A p hp)
            (Spec.map (OneGeneratorSquare.modToExc A f J))
            (Spec.map (OneGeneratorSquare.toMod A J))).symm :=
  rfl

/-- **The comparison of the two composite transition functors of the square of Example 0EVG, at
an object `(ℰ, n)`, is the stage-`n` functor applied to the comparison of the two double
restrictions of `ℰ`.** -/
lemma squareColimVectIso_hom_app (A : Type u) [CommRing A] (f : A) (J : Ideal A) (p : ℕ)
    [Fact p.Prime] (hp : (p : A) = 0) (E : (Spec (CommRingCat.of A)).Vect) (n : ℕ) :
    (squareColimVectIso A f J p hp).hom.app ⟨E, n⟩ =
      EndoColim.stageHomOf (OneGeneratorSquare.frobExc A f J p hp) n
        ((OneGeneratorSquare.squareVectIso A f J).inv.app E) :=
  (congrArg
      (fun i : OneGeneratorSquare.toCentre A f p hp ⋙
            OneGeneratorSquare.centreToExceptional A f J p hp ≅
          OneGeneratorSquare.toModification A J p hp ⋙
            OneGeneratorSquare.modificationToExceptional A f J p hp ↦
        i.hom.app (⟨E, n⟩ : OneGeneratorSquare.colimVectBase A p hp))
      (squareColimVectIso_eq A f J p hp)).trans
    (colimVectSquareIso_hom_app p (OneGeneratorSquare.charExc A f J p hp)
      (OneGeneratorSquare.charBase A p hp) (OneGeneratorSquare.charMod A J p hp)
      (OneGeneratorSquare.charCtr A f p hp) (OneGeneratorSquare.specMap_square A f J)
      (congrArg
        (OneGeneratorSquare.colimVectPullback p (OneGeneratorSquare.charExc A f J p hp)
          (OneGeneratorSquare.charBase A p hp))
        (OneGeneratorSquare.specMap_square A f J).symm) E n)

/-! ### Fullness -/

/-- **A morphism of the colimit category presented by `a₀` is sent to the presented transport of
`a₀`.** -/
private lemma map_eq_hom_of_eq {C : Type u} [Category.{v} C] {C' : Type u₂} [Category.{v} C']
    {F : C ⥤ C} {F' : C' ⥤ C'} {Φ : C ⥤ C'} (α : F ⋙ Φ ≅ Φ ⋙ F') (n k : ℕ) {E G : C}
    {x : (⟨E, n⟩ : EndoColim F) ⟶ ⟨G, n⟩} (a₀ : (F.endoIter (n + k)).obj E ⟶
      (F.endoIter (n + k)).obj G) (ha : EndoColim.Hom.of k a₀ = x) :
    (EndoColim.map F F' Φ α).map x =
      EndoColim.Hom.of k (EndoColim.transportHom F F' Φ α (n + k) a₀) := by
  subst ha
  exact EndoColim.map_map_of _ _ _ _ n k a₀

/-- **The comparison functor of Stacks Tag 0EXC is full** for the one-generator almost blowup
square of Example 0EVG. -/
theorem colimVectComparison_full (A : Type u) [CommRing A] (f : A) (J : Ideal A)
    (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0) :
    (colimVectComparison A f J p hp).Full := by
  refine EndoColim.full_of_surjective_equalStage _ fun m E G w => ?_
  obtain ⟨k, a₀, b₀, ha, hb⟩ := exists_common_presentation_of_pair A f J p hp m w.fst w.snd
  have e₁ := congrArg₂ (· ≫ ·)
    (map_eq_hom_of_eq (OneGeneratorSquare.frobVectIsoCtrExc A f J p hp) m k a₀ ha).symm
    (squareColimVectIso_hom_app A f J p hp G m).symm
  have e₂ := congrArg₂ (· ≫ ·) (squareColimVectIso_hom_app A f J p hp E m)
    (map_eq_hom_of_eq (OneGeneratorSquare.frobVectIsoModExc A f J p hp) m k b₀ hb)
  have hw := e₁.trans (w.w.trans e₂)
  obtain ⟨j, hj⟩ := EndoColim.exists_untransportHom_naturality
    (OneGeneratorSquare.frobBase A p hp) (OneGeneratorSquare.frobExc A f J p hp)
    (OneGeneratorSquare.vectViaCtr A f J) (OneGeneratorSquare.vectViaMod A f J)
    (OneGeneratorSquare.frobVectIsoViaCtr A f J p hp)
    (OneGeneratorSquare.frobVectIsoViaMod A f J p hp)
    (OneGeneratorSquare.squareVectIso A f J).symm
    (OneGeneratorSquare.squareVectIso_symm_compat A f J p hp) m k _ _ hw
  have key : ∃ u : (⟨E, m⟩ : OneGeneratorSquare.colimVectBase A p hp) ⟶ ⟨G, m⟩,
      (OneGeneratorSquare.toCentre A f p hp).map u = w.fst ∧
      (OneGeneratorSquare.toModification A J p hp).map u = w.snd := by
    refine exists_colim_hom_of_pair A f J p hp m w.fst w.snd
      ⟨k + j, _, _, (EndoColim.Hom.of_raise k a₀ j).trans ha,
        (EndoColim.Hom.of_raise k b₀ j).trans hb, ?_⟩
    have hj' := hj (k + j) rfl
    simp only [Iso.symm_hom] at hj'
    rw [EndoColim.untransportHom_endoHomCast_endoRaise_transportHom,
      EndoColim.untransportHom_endoHomCast_endoRaise_transportHom] at hj'
    exact (congrArg (fun t ↦ (OneGeneratorSquare.squareVectIso A f J).hom.app
        (((OneGeneratorSquare.frobBase A p hp).endoIter (m + (k + j))).obj E) ≫ t) hj').trans
      (Iso.hom_inv_id_app_assoc _ _ _)
  obtain ⟨u, hu₁, hu₂⟩ := key
  exact ⟨u, CategoricalPullback.hom_ext hu₁ hu₂⟩

end AlgebraicGeometry

end
