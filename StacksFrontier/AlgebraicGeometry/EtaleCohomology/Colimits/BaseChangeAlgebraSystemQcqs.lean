module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.FiniteCoverKilling
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.FiniteCoverKillingBaseChangeColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleColimitUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtalePresentedSystem

/-!
# Étale cohomology of a base change along a directed system of algebras, qcqs case (Stacks 03Q6)

Let `A` be a ring, `I` a directed set, `(B_i)` a system of `A`-algebras over `I` with colimit
`B`, let `X ⟶ Spec(A)` be quasi-compact and quasi-separated, and let `F` be an abelian sheaf on
`X_étale`. With `Y_i = X ×_{Spec A} Spec B_i`, `Y = X ×_{Spec A} Spec B` and `G_i`, `G` the inverse
images of `F`, [Stacks, Tag 03Q6] asserts `H^p(Y, G) = colim_i H^p(Y_i, G_i)`.

The source proves it as a special case of [Stacks, Tag 09YQ], and so does this file: the library
carries Tag 09YQ on Mathlib's small étale sites for every quasi-compact quasi-separated inverse
system with affine transition morphisms
(`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCohomologyColimit_of_isLimit`). What is
supplied here is the instance of its data:

* the inverse system `i ↦ Y_i` of base changes, its cone with vertex `Y`, and the fact that the
  cone is a limit (`Stacks.EtaleCohomology.QcqsBaseChangeColimit.isLimitLevelCone`) — base change
  along `X ⟶ Spec(A)` commutes with the limit `Spec(B) = lim Spec(B_i)` because the index is
  directed;
* every `Y_i` is quasi-compact and quasi-separated (a base change of `X ⟶ Spec(A)` to the affine
  `Spec(B_i)`), and every transition `Y_j ⟶ Y_i` is affine (a base change of the morphism
  `Spec(B_j) ⟶ Spec(B_i)` of affine schemes);
* the system of inverse images `G_i` of one sheaf along a compatible family of maps to `X`
  (`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.inverseImageEtaleSystem`), whose transition
  maps are the composition isomorphisms of inverse images, and the fact that `G` presents its
  colimit: every leg `f_i^{-1}G_i ⟶ G` is an isomorphism, and over a directed index a compatible
  family of isomorphisms presents the colimit
  (`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimitPresentation_of_isIso`).

Tag 09YQ's conclusion is then exactly the statement of Tag 03Q6: the legs of its cohomology
cocone are the restriction maps `H^p(Y_i, G_i) → H^p(Y, G)` followed by the composition
isomorphism, and its transition maps are the restriction maps `H^p(Y_i, G_i) → H^p(Y_j, G_j)`
followed by an isomorphism of coefficients.

## Main results

* `Stacks.EtaleCohomology.etaleCohomologyBaseChangeColimit` — the statement
  `Stacks.EtaleCohomology.EtaleCohomologyBaseChangeColimit` of Stacks 03Q6, in its geometric form
  (a diagram of affine schemes over an affine base and a limit cone of it).
* `Stacks.EtaleCohomology.etaleCohomology_specBaseChange_colimit` — **Stacks 03Q6**, at the
  source's hypotheses: a ring `A`, a directed system of `A`-algebras with a colimit, and a
  quasi-compact quasi-separated `X ⟶ Spec(A)`.

## References

* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)

Tags covered: 03Q6.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology.SmallEtaleLimitCohomology

/-! ### The system of inverse images of one sheaf -/

section InverseImageSystem

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]
  {X : Scheme.{u}} (q : ∀ i : Iᵒᵖ, D.obj i ⟶ X)
  (hq : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), D.map a ≫ q j = q i)
  (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- **The transition of the system of inverse images of `F`.** For a family `q_i : X_i ⟶ X`
compatible with the transitions of `D`, and `a : i ⟶ j`, the map
`f_a^{-1}(q_j^{-1}F) ⟶ q_i^{-1}F` is the composition isomorphism of inverse images at the
factorisation `q_i = f_a ≫ q_j`. -/
def inverseImageEtaleSystemTransition {i j : Iᵒᵖ} (a : i ⟶ j) :
    (etaleAbelianInverseImage.{u, u + 1} (D.map a)).obj
        ((etaleAbelianInverseImage.{u, u + 1} (q j)).obj F) ⟶
      (etaleAbelianInverseImage.{u, u + 1} (q i)).obj F :=
  ((etaleAbelianInverseImageCompIso'.{u, u + 1} (D.map a) (q j) (q i) (hq a).symm).app F).inv

/-- The associativity pentagon of the composition isomorphisms of inverse images, evaluated at one
sheaf, in the shape of a cocycle condition. -/
private theorem compIso'_hom_app_map_inv_app {X₀ X₁ X₂ X₃ : Scheme.{u}} (f : X₁ ⟶ X₀)
    [HasSheafify (smallEtaleTopology X₀) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology X₁) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology X₂) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology X₃) AddCommGrpCat.{u + 1}]
    (i : X₂ ⟶ X₁) (j : X₃ ⟶ X₂) (a : X₂ ⟶ X₀) (ha : a = i ≫ f) (q : X₃ ⟶ X₁) (hq : q = j ≫ i)
    (p : X₃ ⟶ X₀) (hp₁ : p = q ≫ f) (hp₂ : p = j ≫ a)
    (G : Sheaf (smallEtaleTopology X₀) AddCommGrpCat.{u + 1}) :
    (etaleAbelianInverseImageCompIso'.{u, u + 1} j i q hq).hom.app
        ((etaleAbelianInverseImage.{u, u + 1} f).obj G) ≫
      (etaleAbelianInverseImage.{u, u + 1} j).map
        ((etaleAbelianInverseImageCompIso'.{u, u + 1} i f a ha).inv.app G) ≫
      (etaleAbelianInverseImageCompIso'.{u, u + 1} j a p hp₂).inv.app G =
    (etaleAbelianInverseImageCompIso'.{u, u + 1} q f p hp₁).inv.app G := by
  have h := congrArg (fun e => e.hom.app G)
    (etaleAbelianInverseImageCompIso'_assoc.{u, u + 1} f i j a ha q hq p hp₁ hp₂)
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] at h
  rw [← h, Iso.hom_inv_id_app_assoc]

/-- The cocycle condition of the inverse images of `F`, in the constructed inverse image: it is
the associativity pentagon of the composition isomorphisms. -/
theorem inverseImageEtaleSystemTransition_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    (etaleAbelianInverseImageCompIso'.{u, u + 1} (D.map a) (D.map b) (D.map (a ≫ b))
          (D.map_comp a b)).hom.app ((etaleAbelianInverseImage.{u, u + 1} (q k)).obj F) ≫
        (etaleAbelianInverseImage.{u, u + 1} (D.map a)).map
          (inverseImageEtaleSystemTransition q hq F b) ≫
          inverseImageEtaleSystemTransition q hq F a =
      inverseImageEtaleSystemTransition q hq F (a ≫ b) := by
  simp only [inverseImageEtaleSystemTransition, Iso.app_inv]
  exact compIso'_hom_app_map_inv_app (q k) (D.map b) (D.map a) (q j)
    (hq b).symm (D.map (a ≫ b)) (D.map_comp a b) (q i) (hq (a ≫ b)).symm (hq a).symm F

/-- **The system of inverse images of one sheaf.** For a family `q_i : X_i ⟶ X` compatible with
the transitions of the inverse system `D`, the sheaves `q_i^{-1}F` with the composition
isomorphisms of inverse images as transitions form a system of abelian sheaves in the sense of
[Stacks, Tag 0EZL]. -/
def inverseImageEtaleSystem : EtaleSheafSystem D AddCommGrpCat.{u + 1} where
  obj i := (etaleAbelianInverseImage.{u, u + 1} (q i)).obj F
  map a := (inverseImageIsoPullbackAb (D.map a)).hom.app _ ≫
    inverseImageEtaleSystemTransition q hq F a
  map_comp {i j k} a b := by
    have hco := NatTrans.congr_app (systemPullbackComp_inv_comp (D := D) a b)
      ((etaleAbelianInverseImage.{u, u + 1} (q k)).obj F)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hco
    rw [Functor.map_comp, Category.assoc,
      (inverseImageIsoPullbackAb (D.map a)).hom.naturality_assoc, reassoc_of% hco,
      inverseImageEtaleSystemTransition_comp]

/-- The transition of `inverseImageEtaleSystem`, read in the constructed inverse image, is the
composition isomorphism. -/
theorem systemTransitionMap_inverseImageEtaleSystem {i j : Iᵒᵖ} (a : i ⟶ j) :
    systemTransitionMap (inverseImageEtaleSystem q hq F) a =
      inverseImageEtaleSystemTransition q hq F a := by
  rw [systemTransitionMap_eq]
  exact Iso.inv_hom_id_app_assoc _ _ _

/-- The transitions of `inverseImageEtaleSystem` are isomorphisms. -/
instance isIso_systemTransitionMap_inverseImageEtaleSystem {i j : Iᵒᵖ} (a : i ⟶ j) :
    IsIso (systemTransitionMap (inverseImageEtaleSystem q hq F) a) := by
  rw [systemTransitionMap_inverseImageEtaleSystem]
  exact Iso.isIso_inv _

end InverseImageSystem

/-! ### Presentations by isomorphisms -/

section Presentation

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]
  {c : Cone D} [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}]

/-- **A compatible family of isomorphisms presents the colimit**, over a nonempty directed index:
every compatible family out of the inverse images factors through the inverse of the leg at any
one level, and that level does not matter, because any two levels lie below a common one. -/
theorem isColimitPresentation_of_isIso [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    (𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1})
    (ι : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢)
    (hι : IsCompatibleFamily F 𝒢 ι) (hiso : ∀ i, IsIso (ι i)) :
    IsColimitPresentation F 𝒢 ι where
  compatible := hι
  existsUnique_desc H τ hτ := by
    have := hiso
    have key : ∀ {k i : Iᵒᵖ} (a : k ⟶ i), τ i = ι i ≫ inv (ι k) ≫ τ k := by
      intro k i a
      rw [← hτ a, ← hι a]
      simp
    let i₀ : Iᵒᵖ := op (Classical.arbitrary I)
    refine ⟨inv (ι i₀) ≫ τ i₀, fun i => ?_, fun y hy => (IsIso.eq_inv_comp _).mpr (hy i₀)⟩
    obtain ⟨k, hik, hk₀⟩ := directed_of (· ≤ ·) i.unop i₀.unop
    rw [key (k := op k) (i := i₀) (homOfLE hk₀).op, key (k := op k) (i := i) (homOfLE hik).op]
    simp

end Presentation

end Stacks.EtaleCohomology.SmallEtaleLimitCohomology


/-! ### The system of base changes -/

namespace Stacks.EtaleCohomology.QcqsBaseChangeColimit

variable {I : Type u} [Preorder I] {T : Scheme.{u}} {D : Iᵒᵖ ⥤ Scheme.{u}}

/-- The structure morphism `D_i ⟶ T` of a morphism `s` from `D` to the constant diagram on `T`,
with its target written `T` rather than `((Functor.const Iᵒᵖ).obj T).obj i`. The two are
definitionally equal but not at the transparency instance search and rewriting use, so fibre
products over `T` are formed with this spelling. -/
def baseLeg (s : D ⟶ (Functor.const Iᵒᵖ).obj T) (i : Iᵒᵖ) : D.obj i ⟶ T :=
  s.app i

/-- The structure morphisms commute with the transitions of `D`. -/
theorem map_baseLeg (s : D ⟶ (Functor.const Iᵒᵖ).obj T) {i j : Iᵒᵖ} (a : i ⟶ j) :
    D.map a ≫ baseLeg s j = baseLeg s i :=
  (s.naturality a).trans (Category.comp_id _)

/-- The projection `L ⟶ D_i` of a morphism `c` from the constant diagram on `L` to `D`, with its
source written `L`. -/
def coneLeg {L : Scheme.{u}} (c : (Functor.const Iᵒᵖ).obj L ⟶ D) (i : Iᵒᵖ) : L ⟶ D.obj i :=
  c.app i

/-- The projections commute with the transitions of `D`. -/
theorem coneLeg_map {L : Scheme.{u}} (c : (Functor.const Iᵒᵖ).obj L ⟶ D) {i j : Iᵒᵖ}
    (a : i ⟶ j) : coneLeg c i ≫ D.map a = coneLeg c j :=
  (c.naturality a).symm.trans (Category.id_comp _)

variable (s : D ⟶ (Functor.const Iᵒᵖ).obj T) {X : Scheme.{u}} (g : X ⟶ T)

/-- **The levels `Y_i = D_i ×_T X`** of the base change of the inverse system `D` over `T` along
`g : X ⟶ T`, with transitions the base changes of the transitions of `D`. -/
abbrev levels : Iᵒᵖ ⥤ Scheme.{u} where
  obj i := pullback (baseLeg s i) g
  map {i j} a := pullback.map (baseLeg s i) g (baseLeg s j) g (D.map a) (𝟙 X) (𝟙 T)
    (by rw [Category.comp_id, map_baseLeg]) (by simp)
  map_id i := by
    apply pullback.hom_ext <;> simp
  map_comp a b := by
    apply pullback.hom_ext <;> simp

/-- The projections `Y_i ⟶ X` are compatible with the transitions of the levels. -/
theorem levels_map_snd {i j : Iᵒᵖ} (a : i ⟶ j) :
    (levels s g).map a ≫ pullback.snd (baseLeg s j) g = pullback.snd (baseLeg s i) g := by
  simp

/-- The projections `Y_i ⟶ D_i` are compatible with the transitions of the levels and of `D`. -/
theorem levels_map_fst {i j : Iᵒᵖ} (a : i ⟶ j) :
    (levels s g).map a ≫ pullback.fst (baseLeg s j) g = pullback.fst (baseLeg s i) g ≫ D.map a := by
  simp

/-- Over a directed index, the composite of a cone over the levels with the projection to `X`
does not depend on the level. -/
theorem cone_π_app_snd_eq [IsDirected I (· ≤ ·)] (S : Cone (levels s g)) (i j : Iᵒᵖ) :
    S.π.app i ≫ pullback.snd (baseLeg s i) g = S.π.app j ≫ pullback.snd (baseLeg s j) g := by
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i.unop j.unop
  rw [← S.w (homOfLE hik).op, ← S.w (homOfLE hjk).op, Category.assoc, Category.assoc,
    levels_map_snd, levels_map_snd]

/-- **Every transition of the levels is affine** once the schemes of `D` are: it is a base change
of the transition of `D`, a morphism of affine schemes. -/
instance isAffineHom_levels_map [∀ i, IsAffine (D.obj i)] {i j : Iᵒᵖ} (a : i ⟶ j) :
    IsAffineHom ((levels s g).map a) :=
  have : MorphismProperty.IsStableUnderComposition
      (@IsAffineHom : MorphismProperty Scheme.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative
      (@IsAffineHom : MorphismProperty Scheme.{u})).toIsStableUnderComposition
  MorphismProperty.pullbackMap (P := (@IsAffineHom : MorphismProperty Scheme.{u}))
    (isAffineHom_of_isAffine (D.map a)) (inferInstanceAs (IsAffineHom (𝟙 X)))
    (map_baseLeg s a).symm (Category.id_comp g).symm

/-- **Every level is quasi-compact** when the schemes of `D` are affine and `g` is
quasi-compact. -/
instance compactSpace_levels_obj [∀ i, IsAffine (D.obj i)] [QuasiCompact g] (i : Iᵒᵖ) :
    CompactSpace ((levels s g).obj i) :=
  QuasiCompact.compactSpace_of_compactSpace (pullback.fst (baseLeg s i) g)

/-- **Every level is quasi-separated** when the schemes of `D` are affine and `g` is
quasi-separated. -/
instance quasiSeparatedSpace_levels_obj [∀ i, IsAffine (D.obj i)] [QuasiSeparated g] (i : Iᵒᵖ) :
    QuasiSeparatedSpace ((levels s g).obj i) :=
  quasiSeparatedSpace_of_quasiSeparated (pullback.fst (baseLeg s i) g)

variable {L : Scheme.{u}} (c : (Functor.const Iᵒᵖ).obj L ⟶ D) (sL : L ⟶ T)
  (hsL : ∀ i, sL = coneLeg c i ≫ baseLeg s i)

/-- **The cone of base changes**: the vertex `Y = L ×_T X`, with the base changes of the
projections of the cone `c` as legs. -/
abbrev levelCone : Cone (levels s g) where
  pt := pullback sL g
  π :=
    { app i := pullback.map sL g (baseLeg s i) g (coneLeg c i) (𝟙 X) (𝟙 T)
        (by rw [Category.comp_id, hsL i]) (by simp)
      naturality {i j} a := by
        apply pullback.hom_ext <;> simp [coneLeg_map] }

include hsL in
/-- **The base change of a limit is the limit of the base changes**, over a nonempty directed
index: if `c` is a limit cone of `D`, then `L ×_T X = lim_i D_i ×_T X`. The first component of a
lift is the lift along `c`; the second is the composite with the projection to `X` at any level,
which does not depend on the level because the index is directed. -/
def isLimitLevelCone [Nonempty I] [IsDirected I (· ≤ ·)] (hc : IsLimit (Cone.mk L c)) :
    IsLimit (levelCone s g c sL hsL) := by
  have fac : ∀ (S : Cone D) (j : Iᵒᵖ), hc.lift S ≫ coneLeg c j = S.π.app j :=
    fun S j => hc.fac S j
  have ext : ∀ {W : Scheme.{u}} (f f' : W ⟶ L),
      (∀ j, f ≫ coneLeg c j = f' ≫ coneLeg c j) → f = f' :=
    fun f f' h => hc.hom_ext h
  let base : Cone (levels s g) → Cone D := fun S =>
    { pt := S.pt
      π :=
        { app i := S.π.app i ≫ pullback.fst (baseLeg s i) g
          naturality {i j} a := by
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
              Category.assoc]
            rw [← levels_map_fst, ← Category.assoc, S.w a] } }
  let i₀ : Iᵒᵖ := op (Classical.arbitrary I)
  have w : ∀ S : Cone (levels s g),
      hc.lift (base S) ≫ sL = (S.π.app i₀ ≫ pullback.snd (baseLeg s i₀) g) ≫ g := by
    intro S
    rw [hsL i₀, ← Category.assoc, fac (base S) i₀]
    show (S.π.app i₀ ≫ pullback.fst (baseLeg s i₀) g) ≫ baseLeg s i₀ = _
    rw [Category.assoc, pullback.condition, Category.assoc]
  have lfst : ∀ S : Cone (levels s g),
      pullback.lift _ _ (w S) ≫ pullback.fst sL g = hc.lift (base S) :=
    fun S => pullback.lift_fst _ _ _
  have lsnd : ∀ S : Cone (levels s g),
      pullback.lift _ _ (w S) ≫ pullback.snd sL g = S.π.app i₀ ≫ pullback.snd (baseLeg s i₀) g :=
    fun S => pullback.lift_snd _ _ _
  have πfst : ∀ j, (levelCone s g c sL hsL).π.app j ≫ pullback.fst (baseLeg s j) g =
      pullback.fst sL g ≫ coneLeg c j :=
    fun j => pullback.lift_fst _ _ _
  have πsnd : ∀ j, (levelCone s g c sL hsL).π.app j ≫ pullback.snd (baseLeg s j) g =
      pullback.snd sL g := fun j =>
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  refine
    { lift S := pullback.lift _ _ (w S)
      fac S j := ?_
      uniq S m hm := ?_ }
  · apply pullback.hom_ext
    · rw [Category.assoc, πfst, ← Category.assoc, lfst, fac]
    · rw [Category.assoc, πsnd, lsnd]
      exact cone_π_app_snd_eq s g S i₀ j
  · apply pullback.hom_ext
    · rw [lfst]
      refine ext _ _ fun j => ?_
      rw [fac, Category.assoc, ← πfst, ← Category.assoc, hm j]
    · rw [lsnd, ← hm i₀, Category.assoc, πsnd]

end Stacks.EtaleCohomology.QcqsBaseChangeColimit

namespace Stacks.EtaleCohomology

open SmallEtaleLimitCohomology QcqsBaseChangeColimit

/-- **The statement of Stacks 03Q6 holds**, in its geometric form
`Stacks.EtaleCohomology.EtaleCohomologyBaseChangeColimit`: for an affine `T`, a nonempty directed
inverse system `D` of affine schemes over `T` with a limit `L`, a quasi-compact quasi-separated
`g : X ⟶ T` and an abelian sheaf `F` on `X_étale`, the cohomology of the inverse image of `F` on
`Y = L ×_T X` is the filtered colimit of the cohomology of its inverse images on the
`Y_i = D_i ×_T X`, along the restriction maps.

This is [Stacks, Tag 09YQ] (`SmallEtaleLimitCohomology.isCohomologyColimit_of_isLimit`) at the
inverse system of the `Y_i`, with the system of inverse images of `F`. -/
theorem etaleCohomologyBaseChangeColimit : EtaleCohomologyBaseChangeColimit.{u + 1, 0, u} := by
  intro T _ I _ _ _ D _ s L c hc sL hsL X g _ _ F p
  have hsL' : ∀ i, sL = coneLeg c i ≫ baseLeg s i := hsL
  let q : ∀ i : Iᵒᵖ, (levels s g).obj i ⟶ X := fun i => pullback.snd (baseLeg s i) g
  have hq : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), (levels s g).map a ≫ q j = q i :=
    fun a => levels_map_snd s g a
  have hπq : ∀ i, pullback.snd sL g = conePi (levelCone s g c sL hsL') i ≫ q i :=
    fun i => by simp [conePi, q]
  let ι := fun i : Iᵒᵖ =>
    ((etaleAbelianInverseImageCompIso'.{u, u + 1} (conePi (levelCone s g c sL hsL') i) (q i)
      (pullback.snd sL g) (hπq i)).app F).inv
  have hcompat : IsCompatibleFamily (c := levelCone s g c sL hsL')
      (inverseImageEtaleSystem q hq F)
      ((etaleAbelianInverseImage.{u, u + 1} (pullback.snd sL g)).obj F) ι := by
    intro i j a
    have key := compIso'_hom_app_map_inv_app (q j) ((levels s g).map a)
      (conePi (levelCone s g c sL hsL') i) (q i) (hq a).symm
      (conePi (levelCone s g c sL hsL') j) (conePi_comp (levelCone s g c sL hsL') a).symm
      (pullback.snd sL g) (hπq j) (hπq i) F
    rw [systemTransitionMap_inverseImageEtaleSystem]
    exact key
  have hpres := isColimitPresentation_of_isIso (c := levelCone s g c sL hsL')
    (inverseImageEtaleSystem q hq F)
    ((etaleAbelianInverseImage.{u, u + 1} (pullback.snd sL g)).obj F) ι hcompat
    fun _ => Iso.isIso_inv _
  let E := presentedSystemOfIsColimitPresentation (c := levelCone s g c sL hsL')
    (inverseImageEtaleSystem q hq F)
    ((etaleAbelianInverseImage.{u, u + 1} (pullback.snd sL g)).obj F) ι hpres
  obtain ⟨B, hB⟩ := BigEtaleSite.exists_contains_of_small
    (Set.range (levels s g).obj ∪ {pullback sL g} : Set Scheme.{u})
  have H := isCohomologyColimit_of_isLimit.{u, u} (levels s g) (levelCone s g c sL hsL') B
    (fun i => hB _ (Or.inl ⟨i, rfl⟩)) (hB _ (Or.inr rfl))
    (isLimitLevelCone s g c sL hsL' hc) p E
  refine ⟨fun η => ?_, fun i ξ hξ => ?_⟩
  · obtain ⟨i, ξ, hξ⟩ := H.exists_leg_eq η
    exact ⟨i, ξ, hξ⟩
  · have hξ' : etaleCohomologyRestrictionMap.{u, u + 1, u + 1}
        (conePi (levelCone s g c sL hsL') i) _ p ξ = 0 := hξ
    have hleg : E.leg i p ξ = 0 :=
      (congrArg (Sheaf.H.map (E.ι i) p) hξ').trans (map_zero _)
    obtain ⟨j, a, ha⟩ := H.exists_transition_eq_zero i ξ hleg
    have ha' : (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} ((levels s g).map a) _ p ξ).comp
        (Ext.mk₀ (systemTransitionMap (inverseImageEtaleSystem q hq F) a)) (add_zero p) = 0 := ha
    have := isIso_systemTransitionMap_inverseImageEtaleSystem q hq F a
    exact ⟨j, a, (Stacks.ExtAdjunction.comp_mk₀_eq_zero_iff_of_isIso
      (systemTransitionMap (inverseImageEtaleSystem q hq F) a) _).mp ha'⟩

/-- **[Stacks, Tag 03Q6].** Let `A` be a ring, `I` a nonempty directed set, `(B_i)` a system of
`A`-algebras over `I` (a functor `B : I ⥤ Under A`) and `cB` a colimit cocone of it, with vertex
`B = colim_i B_i`. Let `g : X ⟶ Spec(A)` be quasi-compact and quasi-separated and `F` an abelian
sheaf on `X_étale`. Write `Y_i = Spec(B_i) ×_{Spec A} X`, `Y = Spec(B) ×_{Spec A} X` and `G_i`,
`G` for the inverse images of `F` along the projections to `X`. Then for every `p`,

`H^p_étale(Y, G) = colim_i H^p_étale(Y_i, G_i)`,

the colimit taken along the restriction maps of the morphisms `Y_j ⟶ Y_i` (for `i ≤ j`) and
`Y ⟶ Y_i`. The colimit is stated elementwise, which over a directed index and with abelian
groups is the assertion that the cocone is a colimit: every class on `Y` comes from some `Y_i` (the
inverse image of `G_i` on `Y` identified with `G` by the composition isomorphism of inverse
images), and a class on `Y_i` which dies on `Y` already dies on some `Y_j`, `j ≥ i`.

The proof is the source's: this is [Stacks, Tag 09YQ] at the inverse system of the `Y_i`
(`Stacks.EtaleCohomology.etaleCohomologyBaseChangeColimit`), the limit `Spec(B) = lim Spec(B_i)`
being the image of the colimit `B` under `Spec`. -/
@[stacks 03Q6 "the whole lemma, at the source's hypotheses: a ring `A`, a directed set `I` \
(nonempty, as directed sets are in the source), a system of `A`-algebras `B : I ⥤ Under A` with a \
colimit cocone `cB` (so `B = colim B_i` is `cB.pt`), a quasi-compact and quasi-separated \
`g : X ⟶ Spec A`, an abelian sheaf `F` on Mathlib's small etale site of `X` and every degree `p`. \
`Y_i` and `Y` are the fibre products `Spec B_i ×_{Spec A} X` and `Spec B ×_{Spec A} X` (the \
factors in Mathlib's `pullback` order), `G_i`, `G` the inverse images of `F` along their \
projections to `X`, and the cohomology is the library's etale cohomology `Sheaf.H` on the small \
etale sites, with coefficients in `AddCommGrpCat.{u + 1}`, the first universe in which these \
sites have sheafification. The equality of the source is stated as the elementwise form of a \
filtered colimit of abelian groups along the restriction maps: joint surjectivity of the maps \
`H^p(Y_i, G_i) to H^p(Y, G)` and eventual vanishing of a class killed on `Y`, which over a \
directed index is exactly the assertion that the cohomology cocone is colimiting. The proof is \
the source's, Tag 09YQ at the inverse system of base changes."]
theorem etaleCohomology_specBaseChange_colimit (A : CommRingCat.{u}) (I : Type u) [Preorder I]
    [Nonempty I] [IsDirected I (· ≤ ·)] (B : I ⥤ Under A) (cB : Cocone B) (hcB : IsColimit cB)
    (X : Scheme.{u}) (g : X ⟶ Spec A) [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℕ) :
    (∀ η : Sheaf.H.{u + 1}
        ((etaleAbelianInverseImage.{u, 0} (pullback.snd (Spec.map cB.pt.hom) g)).obj F) p,
      ∃ (i : I)
        (ξ : Sheaf.H.{u + 1}
          ((etaleAbelianInverseImage.{u, 0} (pullback.snd (Spec.map (B.obj i).hom) g)).obj F) p),
        (etaleCohomologyRestrictionMap.{u, 0, u + 1}
          (pullback.map (Spec.map cB.pt.hom) g (Spec.map (B.obj i).hom) g
            (Spec.map (cB.ι.app i).right) (𝟙 X) (𝟙 (Spec A))
            (by rw [Category.comp_id, ← Spec.map_comp, Under.w]; rfl) (by simp)) _ p ξ).comp
          (Ext.mk₀ ((etaleAbelianInverseImageCompIso'.{u, 0}
            (pullback.map (Spec.map cB.pt.hom) g (Spec.map (B.obj i).hom) g
              (Spec.map (cB.ι.app i).right) (𝟙 X) (𝟙 (Spec A))
              (by rw [Category.comp_id, ← Spec.map_comp, Under.w]; rfl) (by simp))
            (pullback.snd (Spec.map (B.obj i).hom) g) (pullback.snd (Spec.map cB.pt.hom) g)
            (by simp only [pullback.map, pullback.lift_snd, Category.comp_id])).app F).inv)
          (add_zero p) = η) ∧
    (∀ (i : I)
        (ξ : Sheaf.H.{u + 1}
          ((etaleAbelianInverseImage.{u, 0} (pullback.snd (Spec.map (B.obj i).hom) g)).obj F) p),
        etaleCohomologyRestrictionMap.{u, 0, u + 1}
          (pullback.map (Spec.map cB.pt.hom) g (Spec.map (B.obj i).hom) g
            (Spec.map (cB.ι.app i).right) (𝟙 X) (𝟙 (Spec A))
            (by rw [Category.comp_id, ← Spec.map_comp, Under.w]; rfl) (by simp)) _ p ξ = 0 →
        ∃ (j : I) (a : i ⟶ j),
          etaleCohomologyRestrictionMap.{u, 0, u + 1}
            (pullback.map (Spec.map (B.obj j).hom) g (Spec.map (B.obj i).hom) g
              (Spec.map (B.map a).right) (𝟙 X) (𝟙 (Spec A))
              (by rw [Category.comp_id, ← Spec.map_comp, Under.w]) (by simp)) _ p ξ = 0) := by
  have : IsConnected I := IsFiltered.isConnected I
  let D : Iᵒᵖ ⥤ Scheme.{u} := (B ⋙ Under.forget A).op ⋙ Scheme.Spec
  have : ∀ i, IsAffine (D.obj i) := fun i => inferInstanceAs (IsAffine (Spec _))
  let s : D ⟶ (Functor.const Iᵒᵖ).obj (Spec A) :=
    { app i := Spec.map (B.obj i.unop).hom
      naturality i j a := by
        show Spec.map (B.map a.unop).right ≫ Spec.map (B.obj j.unop).hom =
          Spec.map (B.obj i.unop).hom ≫ 𝟙 _
        rw [← Spec.map_comp, Under.w, Category.comp_id] }
  let c : (Functor.const Iᵒᵖ).obj (Spec cB.pt.right) ⟶ D :=
    { app i := Spec.map (cB.ι.app i.unop).right
      naturality i j a := by
        show 𝟙 _ ≫ Spec.map (cB.ι.app j.unop).right =
          Spec.map (cB.ι.app i.unop).right ≫ Spec.map (B.map a.unop).right
        rw [← Spec.map_comp, ← Under.comp_right, cB.w, Category.id_comp] }
  have hc : IsLimit (Cone.mk (Spec cB.pt.right) c) :=
    IsLimit.ofIsoLimit (isLimitOfPreserves Scheme.Spec
      (isColimitOfPreserves (Under.forget A) hcB).op)
      (Cone.ext (Iso.refl _) (fun _ => (Category.id_comp _).symm))
  obtain ⟨h₁, h₂⟩ := etaleCohomologyBaseChangeColimit (Spec A) I D s (Spec cB.pt.right) c hc
    (Spec.map cB.pt.hom)
    (fun i => by
      show Spec.map cB.pt.hom =
        Spec.map (cB.ι.app i.unop).right ≫ Spec.map (B.obj i.unop).hom
      rw [← Spec.map_comp, Under.w]; rfl) X g F p
  refine ⟨fun η => ?_, fun i ξ hξ => ?_⟩
  · obtain ⟨i, ξ, h⟩ := h₁ η
    exact ⟨i.unop, ξ, h⟩
  · obtain ⟨j, a, h⟩ := h₂ (op i) ξ hξ
    exact ⟨j.unop, a.unop, h⟩

end Stacks.EtaleCohomology

end
