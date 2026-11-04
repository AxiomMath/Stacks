module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.NormalIntegralCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FirstCohomologyKilling.FiniteEtaleCover
public import StacksFrontier.CategoryTheory.Abelian.ExtMapFunctorial

/-!
# Killing a class on a closed subscheme by a finite cover, via Stacks 03Q6

Let `X` be an affine scheme, `Z ⊂ X` a closed subscheme, `M` a finite abelian group and
`ξ ∈ H^q_etale(Z, M)` with `q ≥ 1`. Part (2) of
[Stacks, Tag 09ZD](https://stacks.math.columbia.edu/tag/09ZD) produces a finite surjective
morphism `X' ⟶ X` of finite presentation along which `ξ` dies on `X' ×_X Z`.

The proof is the source's. Part (1) gives an integral surjective `π : X' ⟶ X` on whose closed
subschemes all positive-degree cohomology with finite constant coefficients vanishes, and Stacks
09YZ writes `π` as the limit of a directed system of finite surjective morphisms `X'_i ⟶ X` of
finite presentation
(`AlgebraicGeometry.exists_integralLimitPresentation_isClosedImmersion_isNormal`). The class `ξ`
dies on `X' ×_X Z`, a closed subscheme of `X'`, and Stacks 03Q6 — the cohomology of
`X' ×_X Z = lim_i X'_i ×_X Z` is the colimit of the cohomology of the stages — makes it die on
some stage `X'_i ×_X Z` already.

## Main definitions and results

* `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_comp_eq_zero_iff` — a class dies under
  restriction along a composite exactly when its restriction along the first map dies under the
  second.
* `Stacks.EtaleCohomology.EtaleCohomologyBaseChangeColimit` — the statement of Stacks 03Q6 in
  the library's étale cohomology `Sheaf.H` on Mathlib's small étale sites, with the transition
  maps of the colimit the restriction maps `etaleCohomologyRestrictionMap`.
* `Stacks.EtaleCohomology.exists_isFinite_surjective_etaleCohomologyRestrictionMap_eq_zero` —
  part (2) of Stacks 09ZD, granted Stacks 03Q6 and the descent statement part (1) carries.

## Implementation notes

**The colimit of Stacks 03Q6 is stated elementwise.** A cocone of abelian groups over a directed
index is a colimit cocone exactly when every element of the vertex comes from some stage and an
element of a stage which dies in the vertex already dies at a later stage. Both halves are the
statement `EtaleCohomologyBaseChangeColimit`; only the second is used for 09ZD (2). The groups of
the colimit are the étale cohomology groups of the base changes `Y_i = Spec(B_i) ×_{Spec A} X`
and `Y = Spec(B) ×_{Spec A} X` with coefficients in the inverse images of `F`, and the maps are
the restriction maps along the morphisms `Y ⟶ Y_i` and `Y_j ⟶ Y_i`, so the statement is about
the library's mainstream étale cohomology; the identification of the inverse image of `G_i`
along `Y ⟶ Y_i` with `G` is `Stacks.EtaleCohomology.etaleAbelianInverseImageCompIso'`. The
system of algebras appears geometrically, as in the library's affine form of the tag
(`Stacks.EtaleCohomology.BaseChangeAlgebraSystem.etaleCohomologyColimit_baseChange_isColimit`): a
diagram `D` of affine schemes over the affine scheme `T = Spec(A)`, `D_i = Spec(B_i)`, and a
limit cone of it with apex `L`, which is `Spec(colim_i B_i)` by Stacks 01YW.

That form of Stacks 03Q6 is not in this library. The tag's library forms compute the cohomology
on the universe-raised small affine étale sites of Stacks 09YP and do not identify the transition
maps of the colimit with restriction maps. Part (2) of 09ZD
therefore takes it as the named argument `h03Q6` and is not registered.

## References

* [Stacks Project, Tag 09ZD](https://stacks.math.columbia.edu/tag/09ZD)
* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry

universe w v u

namespace Stacks.ExtAdjunction

/-- A class precomposed with an isomorphism vanishes exactly when the class does. -/
lemma mk₀_comp_eq_zero_iff_of_isIso {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C]
    {X Y Z : C} (f : X ⟶ Y) [IsIso f] {n : ℕ}
    (y : Ext.{w} Y Z n) : (Ext.mk₀ f).comp y (zero_add n) = 0 ↔ y = 0 := by
  refine ⟨fun h => (precomp_mk₀_bijective_of_isIso f n).1 ?_, fun h => by rw [h, Ext.comp_zero]⟩
  rw [precomp_apply, precomp_apply, Ext.comp_zero]
  exact h

end Stacks.ExtAdjunction

namespace Stacks.EtaleCohomology

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable [∀ S : Scheme.{u}, HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-! ### Restriction along a composite -/

/-- **Vanishing under restriction along a composite.** For `a : Y ⟶ X`, `b : Z ⟶ Y` and
`ab = b ≫ a`, a class `x ∈ H^q(X, F)` dies under restriction along `ab` exactly when its
restriction along `a` dies under restriction along `b`. The two classes differ by the
composition isomorphism `ab⁻¹ ≅ a⁻¹ ⋙ b⁻¹` of inverse images and by the identifications of the
inverse images of the constant sheaf `ℤ`, all of which are invertible. -/
theorem etaleCohomologyRestrictionMap_comp_eq_zero_iff {X Y Z : Scheme.{u}} (a : Y ⟶ X)
    (b : Z ⟶ Y) (ab : Z ⟶ X) (hab : ab = b ≫ a)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) {q : ℕ}
    (x : Sheaf.H.{w} F q) :
    etaleCohomologyRestrictionMap.{u, v, w} b _ q (etaleCohomologyRestrictionMap.{u, v, w} a F q x)
        = 0 ↔
      etaleCohomologyRestrictionMap.{u, v, w} ab F q x = 0 := by
  let ℤX := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
    (AddCommGrpCat.of (ULift ℤ))
  let τ := etaleAbelianInverseImageCompIso'.{u, v} b a ab hab
  have hτ := Stacks.ExtFunctorial.mk₀_comp_mapExactFunctor τ.hom ℤX q x
  have hcomp := Stacks.ExtFunctorial.mapExactFunctor_comp_functor
    (etaleAbelianInverseImage.{u, v} a) (etaleAbelianInverseImage.{u, v} b) ℤX q x
  rw [etaleCohomologyRestrictionMap_apply, etaleCohomologyRestrictionMap_apply,
    etaleCohomologyRestrictionMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  refine (Stacks.ExtAdjunction.mk₀_comp_eq_zero_iff_of_isIso _ _).trans
    ((Stacks.ExtAdjunction.mk₀_comp_eq_zero_iff_of_isIso _ _).trans ?_)
  refine Iff.trans ?_ (Stacks.ExtAdjunction.mk₀_comp_eq_zero_iff_of_isIso _ _).symm
  rw [hcomp, ← Stacks.ExtAdjunction.mk₀_comp_eq_zero_iff_of_isIso (τ.hom.app ℤX)
    (x.mapExactFunctor (etaleAbelianInverseImage.{u, v} a ⋙ etaleAbelianInverseImage.{u, v} b)),
    hτ, Stacks.ExtAdjunction.comp_mk₀_eq_zero_iff_of_isIso]

/-! ### Stacks 03Q6 -/

/-- **The statement of Stacks 03Q6, on Mathlib's small étale sites.** Let `T = Spec(A)` be an
affine scheme, `I` a nonempty directed preorder, `D : Iᵒᵖ ⥤ Scheme` a diagram of affine schemes
over `T` — the spectra of a directed system of `A`-algebras `B_i` — with structure morphisms `s`,
and `L` with cone `c` a limit of `D`, lying over `T` by `sL`: this is `Spec(B)` with
`B = colim_i B_i`. Let `g : X ⟶ T` be quasi-compact and quasi-separated and `F` an abelian sheaf
on `X_étale`. Write `Y_i = D_i ×_T X` and `Y = L ×_T X`, and `G_i`, `G` for the inverse images of
`F` on them. Then for every `p`,

`H^p_étale(Y, G) = colim_i H^p_étale(Y_i, G_i)`,

the colimit being taken along the restriction maps of the morphisms `Y_j ⟶ Y_i` and
`Y ⟶ Y_i`. The colimit is stated elementwise: every class on `Y` comes from a stage (the first
conjunct; the inverse image of `G_i` along `Y ⟶ Y_i` is identified with `G` by the composition
isomorphism of inverse images), and a class on a stage which dies on `Y` already dies on a later
stage (the second). -/
def EtaleCohomologyBaseChangeColimit : Prop :=
  ∀ (T : Scheme.{u}) [IsAffine T] (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] (s : D ⟶ (Functor.const Iᵒᵖ).obj T)
    (L : Scheme.{u}) (c : (Functor.const Iᵒᵖ).obj L ⟶ D) (_ : IsLimit (Cone.mk L c))
    (sL : L ⟶ T) (hsL : ∀ i, sL = c.app i ≫ s.app i)
    (X : Scheme.{u}) (g : X ⟶ T) [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (p : ℕ),
    (∀ η : Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v} (pullback.snd sL g)).obj F) p,
      ∃ (i : Iᵒᵖ)
        (ξ : Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v} (pullback.snd (s.app i) g)).obj F) p),
        (etaleCohomologyRestrictionMap.{u, v, w}
          (pullback.map sL g (s.app i) g (c.app i) (𝟙 X) (𝟙 T)
            (by rw [Category.comp_id, hsL i]) (by simp)) _ p ξ).comp
          (Ext.mk₀ ((etaleAbelianInverseImageCompIso'.{u, v}
            (pullback.map sL g (s.app i) g (c.app i) (𝟙 X) (𝟙 T)
              (by rw [Category.comp_id, hsL i]) (by simp))
            (pullback.snd (s.app i) g) (pullback.snd sL g)
            (by simp only [pullback.map, pullback.lift_snd, Category.comp_id])).app F).inv)
          (add_zero p) = η) ∧
    (∀ (i : Iᵒᵖ)
        (ξ : Sheaf.H.{w} ((etaleAbelianInverseImage.{u, v} (pullback.snd (s.app i) g)).obj F) p),
        etaleCohomologyRestrictionMap.{u, v, w}
          (pullback.map sL g (s.app i) g (c.app i) (𝟙 X) (𝟙 T)
            (by rw [Category.comp_id, hsL i]) (by simp)) _ p ξ = 0 →
        ∃ (j : Iᵒᵖ) (a : j ⟶ i),
          etaleCohomologyRestrictionMap.{u, v, w}
            (pullback.map (s.app j) g (s.app i) g (D.map a) (𝟙 X) (𝟙 T)
              (by simpa using (s.naturality a).symm) (by simp)) _ p ξ = 0)

/-! ### Stacks 09ZD (2) -/

attribute [local instance] AlgebraicGeometry.IntegralLimitPresentation.indexPreorder
  AlgebraicGeometry.IntegralLimitPresentation.indexNonempty
  AlgebraicGeometry.IntegralLimitPresentation.indexDirected

/-- **Part (2) of Stacks 09ZD, granted Stacks 03Q6 and descent.** Let `X` be an affine scheme,
`i : Z ⟶ X` a closed immersion, `M` a finite abelian group and `ξ ∈ H^q_étale(Z, M)` with
`q ≥ 1`. There is a finite surjective morphism `π : X' ⟶ X` of finite presentation such that `ξ`
restricts to zero on `X' ×_X Z`. The coefficient universe `max (u + 1) v` and the `Ext` universe
`w` are arbitrary.

The cover of part (1), `exists_integralLimitPresentation_isClosedImmersion_isNormal`, is the
limit of finite surjective stages `X'_i ⟶ X` of finite presentation (Stacks 09YZ). On
`X' ×_X Z`, a closed subscheme of a closed subscheme of a normal integral affine scheme with
separably closed function field, the cohomology vanishes (part (1),
`subsingleton_etaleH_constantSheaf_of_isClosedImmersion_of_isNormal`), so the restriction of `ξ`
to a stage `X'_i ×_X Z` dies on `X' ×_X Z`, hence by Stacks 03Q6 (`h03Q6`) on a later stage
`X'_j ×_X Z`, and restricting `ξ` to `X'_j ×_X Z` is restricting it to `X'_i ×_X Z` and then to
`X'_j ×_X Z` (`etaleCohomologyRestrictionMap_comp_eq_zero_iff`).

The arguments are Stacks 03Q6 in the form `EtaleCohomologyBaseChangeColimit`, not proved in
this library, and `h0245`, the descent statement part (1) carries (see
`exists_isIntegralHom_surjective_forall_subsingleton_etaleH`); this is not registered as Tag
09ZD (2). -/
theorem exists_isFinite_surjective_etaleCohomologyRestrictionMap_eq_zero
    (h0245 : ∀ B : BigEtaleSite.{u},
      Stacks.EtaleCohomology.EtaleDescentForFiniteEtaleRepresentability B)
    (h03Q6 : EtaleCohomologyBaseChangeColimit.{w, v, u})
    {X Z : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i]
    (M : AddCommGrpCat.{max (u + 1) v}) [Finite M] (q : ℕ) (hq : 0 < q)
    (ξ : Sheaf.H.{w} ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj M)
      q) :
    ∃ (X' : Scheme.{u}) (π : X' ⟶ X), IsFinite π ∧ Surjective π ∧ FinitePresentation π ∧
      etaleCohomologyRestrictionMap.{u, v, w} (pullback.snd π i) _ q ξ = 0 := by
  obtain ⟨X', W, π, j, -, -, hj, hW, hWi, hWn, hWs, P, hPs⟩ :=
    exists_integralLimitPresentation_isClosedImmersion_isNormal X
  have hD : ∀ k, IsAffine (P.diagram.obj k) := fun k =>
    have := P.stageFinite k
    have : IsAffine (((Functor.const P.indexTypeᵒᵖ).obj X).obj k) := inferInstanceAs (IsAffine X)
    isAffine_of_isAffineHom (P.structureMap.app k)
  -- `X' ×_X Z` is a closed subscheme of `W`, so its cohomology with coefficients in `M` vanishes
  have hvan : ∀ G : Sheaf (pullback π i).smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
      (G ≅ (constantSheaf (pullback π i).smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj M) →
        ∀ x : Sheaf.H.{w} G q, x = 0 := by
    intro G e x
    have : IsClosedImmersion (pullback.fst π i) := inferInstance
    have : Subsingleton (Sheaf.H.{w} ((constantSheaf (pullback π i).smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v}).obj M) q) :=
      subsingleton_etaleH_constantSheaf_of_isClosedImmersion_of_isNormal h0245
        (pullback.fst π i ≫ j) M q hq
    exact (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso e.hom q).1 (Subsingleton.elim _ _)
  have hinj := (h03Q6 X P.indexType P.diagram P.structureMap X' P.limitCone P.isLimit π
    P.compatible Z i ((constantSheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj M)
    q).2
  let i₀ : P.indexTypeᵒᵖ := Opposite.op (Classical.arbitrary P.indexType)
  let ξ₀ := etaleCohomologyRestrictionMap.{u, v, w} (pullback.snd (P.structureMap.app i₀) i) _ q ξ
  let m := pullback.map π i (P.structureMap.app i₀) i (P.limitCone.app i₀) (𝟙 Z) (𝟙 X)
    ((Category.comp_id π).trans (P.compatible i₀)) (by simp)
  -- the restriction of `ξ` to the stage `i₀` dies on `X' ×_X Z`, hence on a later stage
  obtain ⟨k, a, hk⟩ := hinj i₀ ξ₀ (hvan _
    ((etaleAbelianInverseImage.{u, v} m).mapIso
        ((etaleAbelianInverseImageConstantIso.{u, v} (pullback.snd (P.structureMap.app i₀) i)).app
          M) ≪≫
      (etaleAbelianInverseImageConstantIso.{u, v} m).app M) _)
  refine ⟨_, P.structureMap.app k, P.stageFinite k, hPs k, P.stageFinitePresentation k, ?_⟩
  exact (etaleCohomologyRestrictionMap_comp_eq_zero_iff _ _ _
    (by simp only [pullback.map, pullback.lift_snd, Category.comp_id]) _ ξ).1 hk

end Stacks.EtaleCohomology

end
