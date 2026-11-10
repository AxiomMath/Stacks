module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.Canonical

/-!
# Reading an isomorphism of inverse images along a morphism

Let `a₁ : W ⟶ Y₁` and `a₂ : W ⟶ Y₂` be morphisms of algebraic spaces and let
`θ : a₁^*M₁ ≅ a₂^*M₂` be an isomorphism of the inverse images of two modules.  For a morphism
`c : Z ⟶ W` the inverse image of `θ` along `c`, read through the comparisons of Stacks 03LU, is
an isomorphism `(c ≫ a₁)^*M₁ ≅ (c ≫ a₂)^*M₂`; this is the *reading* of `θ` along `c`,
`AlgebraicGeometry.Space.QuasiCoherentDescent.readIso`.  The pairwise isomorphisms of a descent
datum read on a test space (`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn`) are
readings.

The reading is stated with the two composites named, `c ≫ a₁ = v₁` and `c ≫ a₂ = v₂`, so that
its type depends on the composites only and not on how they are presented.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.readIso_trans`: reading is compatible with
  composition of isomorphisms.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.readIso_readIso`: reading along `c` and then
  along `w` is reading along `w ≫ c`.  This is the associativity coherence of Stacks 03LU.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.readIso_canonicalComparison`: the reading of a
  canonical comparison is the canonical comparison.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.eq_of_readIso_eq`: reading along an
  isomorphism of algebraic spaces is injective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The reading of an isomorphism of inverse images along a morphism.**  For
`θ : a₁^*M₁ ≅ a₂^*M₂` on `W` and `c : Z ⟶ W` with named composites `v₁ = c ≫ a₁` and
`v₂ = c ≫ a₂`, the inverse image of `θ` along `c` with the comparisons of Stacks 03LU on either
side. -/
def readIso {Z W Y₁ Y₂ : AlgebraicSpaces B S hS} (c : Z ⟶ W) {a₁ : W ⟶ Y₁} {a₂ : W ⟶ Y₂}
    {v₁ : Z ⟶ Y₁} {v₂ : Z ⟶ Y₂} (h₁ : c ≫ a₁ = v₁) (h₂ : c ≫ a₂ = v₂)
    {M₁ : Modules.{u, u} B S hS Y₁.1 Y₁.2} {M₂ : Modules.{u, u} B S hS Y₂.1 Y₂.2}
    (θ : (modulePullback B S hS a₁).obj M₁ ≅ (modulePullback B S hS a₂).obj M₂) :
    (modulePullback B S hS v₁).obj M₁ ≅ (modulePullback B S hS v₂).obj M₂ :=
  pullbackComparison B S hS c a₁ v₁ h₁ M₁ ≪≫ (modulePullback B S hS c).mapIso θ ≪≫
    (pullbackComparison B S hS c a₂ v₂ h₂ M₂).symm

variable {Z W Y₁ Y₂ Y₃ : AlgebraicSpaces B S hS}

/-- The pairwise isomorphism of a descent datum read on a test space is its reading. -/
theorem transitionOn_eq_readIso {I : Type*} {X : AlgebraicSpaces B S hS}
    (Y : I → AlgebraicSpaces B S hS) (f : ∀ i, Y i ⟶ X)
    (F : ∀ i, Modules.{u, u} B S hS (Y i).1 (Y i).2)
    (φ : ∀ i j, (modulePullback B S hS (pairFst B S hS Y f i j)).obj (F i) ≅
      (modulePullback B S hS (pairSnd B S hS Y f i j)).obj (F j))
    {T : AlgebraicSpaces B S hS} (i j : I) (v : T ⟶ pair B S hS Y f i j)
    (vi : T ⟶ Y i) (vj : T ⟶ Y j) (hi : v ≫ pairFst B S hS Y f i j = vi)
    (hj : v ≫ pairSnd B S hS Y f i j = vj) :
    transitionOn B S hS Y f F φ i j v vi vj hi hj = readIso v hi hj (φ i j) :=
  rfl

/-- Reading is compatible with composition of isomorphisms. -/
theorem readIso_trans (c : Z ⟶ W) {a₁ : W ⟶ Y₁} {a₂ : W ⟶ Y₂} {a₃ : W ⟶ Y₃}
    {v₁ : Z ⟶ Y₁} {v₂ : Z ⟶ Y₂} {v₃ : Z ⟶ Y₃} (h₁ : c ≫ a₁ = v₁) (h₂ : c ≫ a₂ = v₂)
    (h₃ : c ≫ a₃ = v₃) {M₁ : Modules.{u, u} B S hS Y₁.1 Y₁.2}
    {M₂ : Modules.{u, u} B S hS Y₂.1 Y₂.2} {M₃ : Modules.{u, u} B S hS Y₃.1 Y₃.2}
    (θ : (modulePullback B S hS a₁).obj M₁ ≅ (modulePullback B S hS a₂).obj M₂)
    (θ' : (modulePullback B S hS a₂).obj M₂ ≅ (modulePullback B S hS a₃).obj M₃) :
    readIso c h₁ h₂ θ ≪≫ readIso c h₂ h₃ θ' = readIso c h₁ h₃ (θ ≪≫ θ') := by
  simp only [readIso, Iso.trans_assoc, Iso.symm_self_id_assoc, Functor.mapIso_trans]

/-- Reading reverses with the isomorphism. -/
theorem readIso_symm (c : Z ⟶ W) {a₁ : W ⟶ Y₁} {a₂ : W ⟶ Y₂}
    {v₁ : Z ⟶ Y₁} {v₂ : Z ⟶ Y₂} (h₁ : c ≫ a₁ = v₁) (h₂ : c ≫ a₂ = v₂)
    {M₁ : Modules.{u, u} B S hS Y₁.1 Y₁.2} {M₂ : Modules.{u, u} B S hS Y₂.1 Y₂.2}
    (θ : (modulePullback B S hS a₁).obj M₁ ≅ (modulePullback B S hS a₂).obj M₂) :
    (readIso c h₁ h₂ θ).symm = readIso c h₂ h₁ θ.symm := by
  simp only [readIso, Iso.trans_symm, Iso.symm_symm_eq, Functor.mapIso_symm, Iso.trans_assoc]

/-- Reading the identity of an inverse image gives the identity. -/
theorem readIso_refl (c : Z ⟶ W) {a₁ : W ⟶ Y₁} {v₁ : Z ⟶ Y₁} (h₁ : c ≫ a₁ = v₁)
    (M₁ : Modules.{u, u} B S hS Y₁.1 Y₁.2) :
    readIso c h₁ h₁ (Iso.refl ((modulePullback B S hS a₁).obj M₁)) = Iso.refl _ := by
  simp only [readIso, Functor.mapIso_refl, Iso.refl_trans, Iso.self_symm_id]

/-- **Reading along `c` and then along `w` is reading along `w ≫ c`.**  This is the associativity
coherence of the comparison of inverse images of Stacks 03LU. -/
theorem readIso_readIso {Z' : AlgebraicSpaces B S hS} (w : Z' ⟶ Z) (c : Z ⟶ W)
    {a₁ : W ⟶ Y₁} {a₂ : W ⟶ Y₂} {v₁ : Z ⟶ Y₁} {v₂ : Z ⟶ Y₂} (h₁ : c ≫ a₁ = v₁)
    (h₂ : c ≫ a₂ = v₂) {u₁ : Z' ⟶ Y₁} {u₂ : Z' ⟶ Y₂} (hw₁ : w ≫ v₁ = u₁) (hw₂ : w ≫ v₂ = u₂)
    {M₁ : Modules.{u, u} B S hS Y₁.1 Y₁.2} {M₂ : Modules.{u, u} B S hS Y₂.1 Y₂.2}
    (θ : (modulePullback B S hS a₁).obj M₁ ≅ (modulePullback B S hS a₂).obj M₂) :
    readIso w hw₁ hw₂ (readIso c h₁ h₂ θ) =
      readIso (w ≫ c) (by rw [Category.assoc, h₁, hw₁]) (by rw [Category.assoc, h₂, hw₂]) θ := by
  subst h₁ h₂ hw₁ hw₂
  change _ = readIso (w ≫ c) (v₁ := (w ≫ c) ≫ a₁) (v₂ := (w ≫ c) ≫ a₂) rfl rfl θ
  rw [readIso, readIso, readIso, Functor.mapIso_trans, Functor.mapIso_trans, Functor.mapIso_symm,
    mapIso_pullbackComparison B S hS w c, mapIso_pullbackComparison B S hS w c]
  simp only [pullbackComparison_rfl, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
  rw [Iso.subst_trans₂ (modulePullbackCompIso_mapIso B S hS w c θ)]
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id, Iso.trans_refl]

/-- **The reading of a canonical comparison is the canonical comparison** of the two inverse
images along the composites. -/
theorem readIso_canonicalComparison {A : AlgebraicSpaces B S hS} (c : Z ⟶ W) {a₁ : W ⟶ Y₁}
    {a₂ : W ⟶ Y₂} {v₁ : Z ⟶ Y₁} {v₂ : Z ⟶ Y₂} (h₁ : c ≫ a₁ = v₁) (h₂ : c ≫ a₂ = v₂)
    (fi : Y₁ ⟶ A) (fj : Y₂ ⟶ A) (h : a₁ ≫ fi = a₂ ≫ fj) (M : Modules.{u, u} B S hS A.1 A.2) :
    readIso c h₁ h₂ (canonicalComparison a₁ a₂ fi fj h M) =
      canonicalComparison v₁ v₂ fi fj
        (by rw [← h₁, ← h₂, Category.assoc, Category.assoc, h]) M := by
  subst h₁ h₂
  exact pair_coherence B S hS c a₁ a₂ fi fj h M

/-- **Reading along an isomorphism of algebraic spaces is injective.** -/
theorem eq_of_readIso_eq (hc : ModulePushforwardCoherence B S hS) (c : Z ⟶ W) [IsIso c]
    {a₁ : W ⟶ Y₁} {a₂ : W ⟶ Y₂} {v₁ : Z ⟶ Y₁} {v₂ : Z ⟶ Y₂} (h₁ : c ≫ a₁ = v₁)
    (h₂ : c ≫ a₂ = v₂) {M₁ : Modules.{u, u} B S hS Y₁.1 Y₁.2}
    {M₂ : Modules.{u, u} B S hS Y₂.1 Y₂.2}
    {θ θ' : (modulePullback B S hS a₁).obj M₁ ≅ (modulePullback B S hS a₂).obj M₂}
    (h : readIso c h₁ h₂ θ = readIso c h₁ h₂ θ') : θ = θ' := by
  have hmap : (modulePullback B S hS c).mapIso θ = (modulePullback B S hS c).mapIso θ' := by
    have h' := congrArg (fun e => (pullbackComparison B S hS c a₁ v₁ h₁ M₁).symm ≪≫ e ≪≫
      pullbackComparison B S hS c a₂ v₂ h₂ M₂) h
    simpa only [readIso, Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id,
      Iso.trans_refl] using h'
  have : (modulePullback B S hS c).Faithful :=
    (ModulePushforwardCoherence.modulePullbackEquivalence hc (asIso c)).faithful_functor
  exact Iso.ext ((modulePullback B S hS c).map_injective (congrArg Iso.hom hmap))

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
