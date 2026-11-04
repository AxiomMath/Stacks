module

public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.EtaleMorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FundamentalExactSequenceSections

/-!
# The order of vanishing on the generic fibre is natural in the étale scheme

The second map of the fundamental exact sequence of Stacks 03RI takes a section of `j_* 𝐆_{m,η}`
over an étale `X`-scheme `U` — an invertible global function on the generic fibre `U ×_X η` — to
its orders of vanishing at the points of `U`. For that family to be a morphism of étale sheaves
rather than a family of maps on sections it must be natural in `U`, and this file proves that
naturality for the irreducible objects of the small étale site, where the order of vanishing is
defined.

Two statements carry the content.

The first is the compatibility of the comparison
`Stacks.EtaleCohomology.genericFibreToFunctionField`, which reads a global function on the
generic fibre of `U` as a rational function on `U`, with pullback along a flat dominant
`w : V ⟶ U`: the rational function read on `V` after restricting to the generic fibre of `V` is
the restriction along `w` of the rational function read on `U`. The comparison is a germ at the
unique point of the generic fibre above the generic point of `U`, carried across the isomorphism
of local rings induced by the projection, so the statement is a commuting diagram of germs and
stalk maps. The one step that needs care is that the generic fibre point of `V` is sent to that
of `U`, which holds because `w` carries the generic point of `V` to the generic point of `U` and
the projection from the generic fibre is injective on points.

The second is the resulting invariance of the order of vanishing, which is
`Stacks.Chow.ord_dominantFunctionFieldMap_eq_ord_base_of_etale` — the order of vanishing of a
rational function at a point of an étale `X`-scheme is its order of vanishing at the image point
— fed by the first.

## Main results

* `Stacks.EtaleCohomology.isDominant_of_flat`: a flat morphism of irreducible schemes is
  dominant, which is what makes the function-field map available.
* `Stacks.EtaleCohomology.stalkCongr_inv_comp_stalkMap_comp`: a commuting square of schemes
  transports stalks compatibly, the stalk-level form of the naturality.
* `Stacks.EtaleCohomology.germ_eq_genericFibreToFunctionField`: the comparison to the function
  field computed at an arbitrary point of the generic fibre above the generic point.
* `Stacks.EtaleCohomology.genericFibreToFunctionField_appTop_of_flat_over`: **the comparison
  is natural**.
* `Stacks.EtaleCohomology.genericFibreOrd_appTop_of_etale_over` and
  `Stacks.EtaleCohomology.etaleGenericFibreOrd_restrict`: **the order of vanishing on the generic
  fibre is natural in the étale `X`-scheme**, in the form the fundamental exact sequence needs.

## Implementation notes

`Stacks.EtaleCohomology.germ_eq_genericFibreToFunctionField` is stated at an arbitrary point `z`
of the generic fibre lying over the generic point, not at
`Stacks.EtaleCohomology.genericFibrePoint`. That is what removes the transport of a point in the
naturality proof: the point used there is the image of the generic fibre point of `V`, and were
the lemma stated only at the chosen point one would have to carry the equality of the two through
every stalk in the diagram.

`Stacks.EtaleCohomology.stalkCongr_inv_comp_stalkMap_comp` takes the two generic points as
variables with their defining equalities as hypotheses, so that both can be substituted away; the
only equality left after that is the one coming from the commuting square, which
`AlgebraicGeometry.Scheme.Hom.stalkMap_congr_hom` handles.

## References

* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI): the fundamental exact
  sequence, whose second map is the order of vanishing at the closed points.
* [Stacks Project, Tag 02JU](https://stacks.math.columbia.edu/tag/02JU): the function field of a
  dominant morphism of integral schemes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Order TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

section Dominant

/-- A flat morphism of irreducible schemes is dominant. -/
theorem isDominant_of_flat {A B : Scheme.{u}} [IrreducibleSpace A] [IrreducibleSpace B]
    (f : A ⟶ B) [Flat f] : IsDominant f := by
  refine ⟨?_⟩
  have h : closure {genericPoint B} ⊆ closure (Set.range f.base) :=
    closure_mono (Set.singleton_subset_iff.2
      ⟨genericPoint A, base_genericPoint_eq_genericPoint_of_flat f⟩)
  rw [genericPoint_spec B] at h
  exact dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset h)

end Dominant

section StalkSquare

/-- A commuting square of schemes transports stalks compatibly. -/
theorem stalkCongr_inv_comp_stalkMap_comp {A B C D : Scheme.{u}}
    (pA : C ⟶ A) (pB : D ⟶ B) (q : D ⟶ C) (w : B ⟶ A) (hq : q ≫ pA = pB ≫ w)
    (zD : D) (ηB : B) (ηA : A) (hB : pB.base zD = ηB) (hA : w.base ηB = ηA)
    (hz : pA.base (q.base zD) = ηA) :
    (A.presheaf.stalkCongr (Inseparable.of_eq hz)).inv ≫
        pA.stalkMap (q.base zD) ≫ q.stalkMap zD =
      eqToHom (congrArg A.presheaf.stalk hA.symm) ≫ w.stalkMap ηB ≫
        (B.presheaf.stalkCongr (Inseparable.of_eq hB)).inv ≫ pB.stalkMap zD := by
  subst hA
  subst hB
  have hkey : pA.stalkMap (q.base zD) ≫ q.stalkMap zD =
      (A.presheaf.stalkCongr (Inseparable.of_eq hz)).hom ≫
        w.stalkMap (pB.base zD) ≫ pB.stalkMap zD :=
    (Scheme.Hom.stalkMap_comp q pA zD).symm.trans
      ((Scheme.Hom.stalkMap_congr_hom (q ≫ pA) (pB ≫ w) hq zD).trans
        (congrArg (fun m : A.presheaf.stalk (w.base (pB.base zD)) ⟶ D.presheaf.stalk zD =>
          (A.presheaf.stalkCongr (Inseparable.of_eq hz)).hom ≫ m)
          (Scheme.Hom.stalkMap_comp pB w zD)))
  rw [hkey, Iso.inv_hom_id_assoc]
  simp

end StalkSquare

section Comparison

variable {X : Scheme.{u}} [IrreducibleSpace X] {U : Scheme.{u}} [IrreducibleSpace U]
  (g : U ⟶ X) [Flat g]

/-- The germ at a point of the generic fibre lying over the generic point of `U` factors through
the comparison `Stacks.EtaleCohomology.genericFibreToFunctionField`. -/
theorem germ_eq_genericFibreToFunctionField
    (z : ↥(pullback g (genericPointInclusion X)))
    (hz : (pullback.fst g (genericPointInclusion X)).base z = genericPoint U) :
    (pullback g (genericPointInclusion X)).presheaf.germ ⊤ z trivial =
      genericFibreToFunctionField g ≫ (U.presheaf.stalkCongr (Inseparable.of_eq hz)).inv ≫
        (pullback.fst g (genericPointInclusion X)).stalkMap z := by
  obtain rfl := eq_genericFibrePoint g hz
  have := isIso_stalkMap_pullback_fst_genericPointInclusion X g (genericFibrePoint g)
  simp only [genericFibreToFunctionField, Category.assoc, Iso.hom_inv_id_assoc,
    IsIso.inv_hom_id, Category.comp_id]

variable {V : Scheme.{u}} [IrreducibleSpace V] (gV : V ⟶ X) [Flat gV]

/-- **A function on the generic fibre is read as a rational function compatibly with pullback.**
For `w : V ⟶ U` a flat dominant morphism of integral schemes over `X` and `q` the induced
morphism of generic fibres, restricting a global function on the generic fibre of `U` to the
generic fibre of `V` and reading it as a rational function on `V` is the same as reading it as a
rational function on `U` and restricting that along `w`. -/
theorem genericFibreToFunctionField_appTop_of_flat_over [AlgebraicGeometry.IsIntegral U]
    [AlgebraicGeometry.IsIntegral V] (w : V ⟶ U) [Flat w] [IsDominant w]
    (q : pullback gV (genericPointInclusion X) ⟶ pullback g (genericPointInclusion X))
    (hq : q ≫ pullback.fst g (genericPointInclusion X) =
      pullback.fst gV (genericPointInclusion X) ≫ w)
    (a : Γ(pullback g (genericPointInclusion X), ⊤)) :
    genericFibreToFunctionField gV (q.appTop a) =
      dominantFunctionFieldMap w (genericFibreToFunctionField g a) := by
  have hgen : w.base (genericPoint V) = genericPoint U :=
    base_genericPoint_eq_genericPoint_of_flat w
  have hV : (pullback.fst gV (genericPointInclusion X)).base (genericFibrePoint gV) =
      genericPoint V := fst_base_genericFibrePoint gV
  have hsq := congrArg
    (fun φ : pullback gV (genericPointInclusion X) ⟶ U => φ.base (genericFibrePoint gV)) hq
  have hz : (pullback.fst g (genericPointInclusion X)).base
      (q.base (genericFibrePoint gV)) = genericPoint U := by
    refine hsq.trans ?_
    show w.base ((pullback.fst gV (genericPointInclusion X)).base (genericFibrePoint gV)) = _
    rw [hV, hgen]
  have hisoV := isIso_stalkMap_pullback_fst_genericPointInclusion X gV (genericFibrePoint gV)
  have hfield : dominantFunctionFieldMap w =
      (eqToHom (congrArg U.presheaf.stalk hgen.symm) ≫ w.stalkMap (genericPoint V)).hom := by
    rw [dominantFunctionFieldMap,
      Stacks.Chow.stalkMap_eqToHom_eq_cast w (genericPoint V) _ hgen]
  have hgermq : q.appTop ≫ (pullback gV (genericPointInclusion X)).presheaf.germ ⊤
        (genericFibrePoint gV) trivial =
      (pullback g (genericPointInclusion X)).presheaf.germ ⊤
          (q.base (genericFibrePoint gV)) trivial ≫ q.stalkMap (genericFibrePoint gV) :=
    (Scheme.Hom.germ_stalkMap q ⊤ (genericFibrePoint gV) trivial).symm
  have hgermV := germ_eq_genericFibreToFunctionField gV (genericFibrePoint gV) hV
  have hgermU := germ_eq_genericFibreToFunctionField g (q.base (genericFibrePoint gV)) hz
  have hsquare := stalkCongr_inv_comp_stalkMap_comp
    (pullback.fst g (genericPointInclusion X)) (pullback.fst gV (genericPointInclusion X))
    q w hq (genericFibrePoint gV) (genericPoint V) (genericPoint U) hV hgen hz
  have hmor : q.appTop ≫ genericFibreToFunctionField gV =
      genericFibreToFunctionField g ≫
        eqToHom (congrArg U.presheaf.stalk hgen.symm) ≫ w.stalkMap (genericPoint V) := by
    rw [← cancel_mono ((V.presheaf.stalkCongr (Inseparable.of_eq hV)).inv ≫
      (pullback.fst gV (genericPointInclusion X)).stalkMap (genericFibrePoint gV)),
      Category.assoc, Category.assoc, ← hgermV, hgermq, hgermU, Category.assoc,
      Category.assoc, hsquare]
    simp only [Category.assoc]
  rw [hfield]
  exact congrArg
    (fun φ : Γ(pullback g (genericPointInclusion X), ⊤) ⟶ V.functionField => φ.hom a) hmor

end Comparison

section Ord

variable {X : Scheme.{u}} [IrreducibleSpace X] {U V : Scheme.{u}}
  [AlgebraicGeometry.IsIntegral U] [AlgebraicGeometry.IsIntegral V] [IsLocallyNoetherian U]
  [IsLocallyNoetherian V] (g : U ⟶ X) [Flat g] (gV : V ⟶ X) [Flat gV]

/-- **The order of vanishing of a section of `j_* 𝐆_{m,η}` is natural in the étale scheme.** -/
theorem genericFibreOrd_appTop_of_etale_over (w : V ⟶ U) [AlgebraicGeometry.Etale w] [IsDominant w]
    (q : pullback gV (genericPointInclusion X) ⟶ pullback g (genericPointInclusion X))
    (hq : q ≫ pullback.fst g (genericPointInclusion X) =
      pullback.fst gV (genericPointInclusion X) ≫ w)
    (y : V) (a : (Γ(pullback g (genericPointInclusion X), ⊤))ˣ) :
    genericFibreOrd gV y (Additive.ofMul (Units.map q.appTop.hom.toMonoidHom a)) =
      genericFibreOrd g (w.base y) (Additive.ofMul a) := by
  rw [genericFibreOrd_apply, genericFibreOrd_apply]
  show Scheme.ord (genericFibreToFunctionField gV
    (q.appTop (a : Γ(pullback g (genericPointInclusion X), ⊤)))) y = _
  rw [genericFibreToFunctionField_appTop_of_flat_over g gV w q hq]
  exact Stacks.Chow.ord_dominantFunctionFieldMap_eq_ord_base_of_etale w _ y

end Ord

section EtaleSite

variable {X : Scheme.{u}} [IrreducibleSpace X] {U V : X.Etale}
  [AlgebraicGeometry.IsIntegral U.left] [AlgebraicGeometry.IsIntegral V.left]
  [IsLocallyNoetherian U.left] [IsLocallyNoetherian V.left]

omit [IrreducibleSpace X] in
/-- The morphism of base changes induced by a morphism of the small étale site commutes with the
projections to the étale schemes. -/
theorem smallEtaleBaseChange_map_left_comp_fst {Y : Scheme.{u}} (f : Y ⟶ X) {U' V' : X.Etale}
    (h : V' ⟶ U') :
    ((smallEtaleBaseChange f).map h).left ≫ pullback.fst U'.hom f =
      pullback.fst V'.hom f ≫ h.left :=
  pullback.lift_fst _ _ _

/-- **The order of vanishing on an irreducible étale `X`-scheme is natural**: restricting a
global function on the generic fibre of `U` to the generic fibre of `V` along `h : V ⟶ U` and
taking its order of vanishing at a point of `V` gives the order of vanishing of the original
function at the image point of `U`. -/
theorem etaleGenericFibreOrd_restrict (h : V ⟶ U) (y : V.left)
    (a : (Γ(pullback U.hom (genericPointInclusion X), ⊤))ˣ) :
    etaleGenericFibreOrd V y (Additive.ofMul (Units.map
        (((smallEtaleBaseChange (genericPointInclusion X)).map h).left).appTop.hom.toMonoidHom
          a)) =
      etaleGenericFibreOrd U (h.left.base y) (Additive.ofMul a) := by
  have hintU : AlgebraicGeometry.IsIntegral ((𝟭 Scheme).obj U.left) :=
    inferInstanceAs (AlgebraicGeometry.IsIntegral U.left)
  have hintV : AlgebraicGeometry.IsIntegral ((𝟭 Scheme).obj V.left) :=
    inferInstanceAs (AlgebraicGeometry.IsIntegral V.left)
  have hlnU : IsLocallyNoetherian ((𝟭 Scheme).obj U.left) :=
    inferInstanceAs (IsLocallyNoetherian U.left)
  have hlnV : IsLocallyNoetherian ((𝟭 Scheme).obj V.left) :=
    inferInstanceAs (IsLocallyNoetherian V.left)
  have hdom : IsDominant h.left := isDominant_of_flat h.left
  have hirrU : IrreducibleSpace ↥((Functor.fromPUnit X).obj U.right) :=
    inferInstanceAs (IrreducibleSpace ↥X)
  exact genericFibreOrd_appTop_of_etale_over U.hom V.hom h.left _
    (smallEtaleBaseChange_map_left_comp_fst (genericPointInclusion X) h) y a

end EtaleSite

end Stacks.EtaleCohomology

end
