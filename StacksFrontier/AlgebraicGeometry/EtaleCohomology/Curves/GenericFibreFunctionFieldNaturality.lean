module

public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.Etale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.FundamentalExactSequenceSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Cancellation

/-!
# The comparison with the function field is natural in the `X`-scheme

Let `X` be irreducible with generic point `η` and function field `K`, and let `j : Spec K ⟶ X` be
the inclusion of the generic point. For a flat `g : U ⟶ X` with `U` irreducible,
`Stacks.EtaleCohomology.genericFibreToFunctionField g` reads a global function on the generic
fibre `U ×_X Spec K` as an element of the function field `R(U)`. A morphism `h : U ⟶ V` of
`X`-schemes induces a morphism `U ×_X Spec K ⟶ V ×_X Spec K` of generic fibres, and the square

```
Γ(V ×_X Spec K, ⊤) ⟶ R(V)
        ↓               ↓
Γ(U ×_X Spec K, ⊤) ⟶ R(U)
```

whose right-hand map is `AlgebraicGeometry.dominantFunctionFieldMap h` commutes. Consequently, when
`h` is étale, the order of vanishing at a point of `U` of the restriction of a section of
`j_* 𝐆_{m,K}` over `V` is its order of vanishing at the image point in `V`.

## Main definitions

* `Stacks.EtaleCohomology.genericFibreMap`: the morphism of generic fibres induced by a morphism
  of `X`-schemes.
* `Stacks.EtaleCohomology.etaleGenericFibreMap`: the same, for a morphism of the small étale site
  of `X`.

## Main results

* `Stacks.EtaleCohomology.genericFibreToFunctionField_eq_germ_comp`: the comparison is the germ at
  *any* point of the generic fibre over the generic point of the source, followed by the inverse
  of the stalk map of the projection.
* `Stacks.EtaleCohomology.genericFibreToFunctionField_appTop`,
  `Stacks.EtaleCohomology.comp_appTop_genericFibreToFunctionField`: **the comparison is natural in
  the `X`-scheme.**
* `Stacks.EtaleCohomology.genericFibreOrd_appTop`: **the order of vanishing of a global function
  on the generic fibre is compatible with restriction along an étale morphism of `X`-schemes.**
* `Stacks.EtaleCohomology.etaleGenericFibreOrd_appTop`: the same, for a morphism of the small
  étale site of `X`.

## References

* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI): the fundamental exact
  sequence, whose second map is the order of vanishing at the closed points.
* [Stacks Project, Tag 02JU](https://stacks.math.columbia.edu/tag/02JU): the extension of
  function fields induced by a dominant morphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- A commuting square whose two horizontal maps are isomorphisms, transposed across them. -/
private theorem inv_comp_of_comm_sq {C : Type*} [Category C] {A B A' B' : C}
    (a : A ⟶ A') [IsIso a] (b : A' ⟶ B') (d : A ⟶ B) (c : B ⟶ B') [IsIso c]
    (H : a ≫ b = d ≫ c) : b ≫ inv c = inv a ≫ d := by
  rwa [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]

/-- The stalk map of a morphism read along an equality of morphisms. -/
private theorem stalkMap_congr_of_eq {A D : Scheme.{u}} {f f' : A ⟶ D} (e : f = f') (x : A)
    (E : D.presheaf.stalk (f.base x) = D.presheaf.stalk (f'.base x)) :
    f.stalkMap x = eqToHom E ≫ f'.stalkMap x := by
  subst e
  simp

/-- The stalk map of `h` at a point equal to the generic point of the source, read between the
stalks at the generic points. -/
private theorem stalkCongr_comp_stalkMap_comp_stalkCongr {U V : Scheme.{u}}
    [IrreducibleSpace U] [IrreducibleSpace V] (h : U ⟶ V) {x : U} (hx : x = genericPoint U)
    {b : V} (e : b = h.base x) (hb : b = genericPoint V)
    (e' : genericPoint V = h.base (genericPoint U)) :
    eqToHom (congrArg V.presheaf.stalk e) ≫ h.stalkMap x ≫
        (U.presheaf.stalkCongr (Inseparable.of_eq hx)).hom =
      (V.presheaf.stalkCongr (Inseparable.of_eq hb)).hom ≫
        eqToHom (congrArg V.presheaf.stalk e') ≫ h.stalkMap (genericPoint U) := by
  subst hx
  subst hb
  simp only [Stacks.Chow.stalkCongr_eq_eqToHom, eqToHom_refl, Category.comp_id,
    Category.id_comp]

/-! ### The germ factorisation at an arbitrary point over the generic point -/

/-- **The comparison with the function field is the germ at any point of the generic fibre lying
over the generic point of the source**, followed by the inverse of the isomorphism of local rings
the projection induces there and the identification of the stalk with the function field. -/
theorem genericFibreToFunctionField_eq_germ_comp {X U : Scheme.{u}} [IrreducibleSpace X]
    [IrreducibleSpace U] (g : U ⟶ X) [Flat g]
    {z : ↥(pullback g (genericPointInclusion X))}
    [IsIso ((pullback.fst g (genericPointInclusion X)).stalkMap z)]
    (hz : (pullback.fst g (genericPointInclusion X)).base z = genericPoint U) :
    genericFibreToFunctionField g =
      (pullback g (genericPointInclusion X)).presheaf.germ ⊤ z trivial ≫
        inv ((pullback.fst g (genericPointInclusion X)).stalkMap z) ≫
          (U.presheaf.stalkCongr (Inseparable.of_eq hz)).hom := by
  obtain rfl := eq_genericFibrePoint g hz
  rfl

/-! ### The morphism of generic fibres induced by a morphism of `X`-schemes -/

/-- **The morphism of generic fibres induced by a morphism of `X`-schemes.** -/
def genericFibreMap {X U V : Scheme.{u}} [IrreducibleSpace X] {gU : U ⟶ X} {gV : V ⟶ X}
    (h : U ⟶ V) (hcomm : h ≫ gV = gU) :
    pullback gU (genericPointInclusion X) ⟶ pullback gV (genericPointInclusion X) :=
  pullback.map gU (genericPointInclusion X) gV (genericPointInclusion X) h (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, ← hcomm]) (by rw [Category.comp_id, Category.id_comp])

/-- The morphism of generic fibres induced by `h` lies over `h`: composing it with the first
projection to `V` equals the first projection to `U` followed by `h`. -/
@[simp]
theorem genericFibreMap_comp_fst {X U V : Scheme.{u}} [IrreducibleSpace X] {gU : U ⟶ X}
    {gV : V ⟶ X} (h : U ⟶ V) (hcomm : h ≫ gV = gU) :
    genericFibreMap h hcomm ≫ pullback.fst gV (genericPointInclusion X) =
      pullback.fst gU (genericPointInclusion X) ≫ h := by
  simp [genericFibreMap]

/-! ### Naturality of the comparison -/

/-- The naturality square, with the map on function fields in its stalk-map spelling. -/
private theorem appTop_comp_genericFibreToFunctionField_aux {X U V : Scheme.{u}}
    [IrreducibleSpace X] [IrreducibleSpace U] [IrreducibleSpace V] (gU : U ⟶ X) (gV : V ⟶ X)
    [Flat gU] [Flat gV] (h : U ⟶ V)
    (m : pullback gU (genericPointInclusion X) ⟶ pullback gV (genericPointInclusion X))
    (hm : m ≫ pullback.fst gV (genericPointInclusion X) =
      pullback.fst gU (genericPointInclusion X) ≫ h)
    (hη : genericPoint V = h.base (genericPoint U)) :
    m.appTop ≫ genericFibreToFunctionField gU =
      genericFibreToFunctionField gV ≫ eqToHom (congrArg V.presheaf.stalk hη) ≫
        h.stalkMap (genericPoint U) := by
  have isoU := isIso_stalkMap_pullback_fst_genericPointInclusion X gU (genericFibrePoint gU)
  have isoV := isIso_stalkMap_pullback_fst_genericPointInclusion X gV
    (m.base (genericFibrePoint gU))
  have hzU : (pullback.fst gU (genericPointInclusion X)).base (genericFibrePoint gU) =
      genericPoint U := fst_base_genericFibrePoint gU
  have hbase : (pullback.fst gV (genericPointInclusion X)).base
        (m.base (genericFibrePoint gU)) =
      h.base ((pullback.fst gU (genericPointInclusion X)).base (genericFibrePoint gU)) :=
    congrArg (fun φ : pullback gU (genericPointInclusion X) ⟶ V =>
      φ.base (genericFibrePoint gU)) hm
  have hwV : (pullback.fst gV (genericPointInclusion X)).base
      (m.base (genericFibrePoint gU)) = genericPoint V :=
    hbase.trans ((congrArg h.base hzU).trans hη.symm)
  have hgerm : m.appTop ≫
      (pullback gU (genericPointInclusion X)).presheaf.germ ⊤ (genericFibrePoint gU) trivial =
        (pullback gV (genericPointInclusion X)).presheaf.germ ⊤
          (m.base (genericFibrePoint gU)) trivial ≫ m.stalkMap (genericFibrePoint gU) :=
    (Scheme.Hom.germ_stalkMap m ⊤ (genericFibrePoint gU) trivial).symm
  have hsq : (pullback.fst gV (genericPointInclusion X)).stalkMap
        (m.base (genericFibrePoint gU)) ≫ m.stalkMap (genericFibrePoint gU) =
      eqToHom (congrArg V.presheaf.stalk hbase) ≫
        h.stalkMap ((pullback.fst gU (genericPointInclusion X)).base (genericFibrePoint gU)) ≫
          (pullback.fst gU (genericPointInclusion X)).stalkMap (genericFibrePoint gU) := by
    rw [← Scheme.Hom.stalkMap_comp m (pullback.fst gV (genericPointInclusion X))
        (genericFibrePoint gU),
      ← Scheme.Hom.stalkMap_comp (pullback.fst gU (genericPointInclusion X)) h
        (genericFibrePoint gU)]
    exact stalkMap_congr_of_eq hm (genericFibrePoint gU)
      (congrArg V.presheaf.stalk hbase)
  have hinv := inv_comp_of_comm_sq
    ((pullback.fst gV (genericPointInclusion X)).stalkMap (m.base (genericFibrePoint gU)))
    (m.stalkMap (genericFibrePoint gU))
    (eqToHom (congrArg V.presheaf.stalk hbase) ≫
      h.stalkMap ((pullback.fst gU (genericPointInclusion X)).base (genericFibrePoint gU)))
    ((pullback.fst gU (genericPointInclusion X)).stalkMap (genericFibrePoint gU))
    (by rw [hsq, Category.assoc])
  have htail : m.stalkMap (genericFibrePoint gU) ≫
        inv ((pullback.fst gU (genericPointInclusion X)).stalkMap (genericFibrePoint gU)) ≫
          (U.presheaf.stalkCongr (Inseparable.of_eq hzU)).hom =
      inv ((pullback.fst gV (genericPointInclusion X)).stalkMap
          (m.base (genericFibrePoint gU))) ≫
        (V.presheaf.stalkCongr (Inseparable.of_eq hwV)).hom ≫
          eqToHom (congrArg V.presheaf.stalk hη) ≫ h.stalkMap (genericPoint U) := by
    rw [← Category.assoc, hinv, Category.assoc, Category.assoc,
      stalkCongr_comp_stalkMap_comp_stalkCongr h hzU hbase hwV hη]
  rw [genericFibreToFunctionField_eq_germ_comp gU hzU, reassoc_of% hgerm, htail,
    genericFibreToFunctionField_eq_germ_comp gV hwV]
  simp only [Category.assoc]

/-- **The comparison with the function field is natural in the `X`-scheme.** A global function on
the generic fibre of `V`, restricted along a morphism `m` of generic fibres over `h : U ⟶ V` and
then read as a rational function on `U`, is the image under
`AlgebraicGeometry.dominantFunctionFieldMap h` of the rational function it defines on `V`. -/
theorem genericFibreToFunctionField_appTop {X U V : Scheme.{u}} [IrreducibleSpace X]
    [IsIntegral U] [IsIntegral V] (gU : U ⟶ X) (gV : V ⟶ X) [Flat gU] [Flat gV]
    (h : U ⟶ V) [IsDominant h]
    (m : pullback gU (genericPointInclusion X) ⟶ pullback gV (genericPointInclusion X))
    (hm : m ≫ pullback.fst gV (genericPointInclusion X) =
      pullback.fst gU (genericPointInclusion X) ≫ h)
    (a : Γ(pullback gV (genericPointInclusion X), ⊤)) :
    genericFibreToFunctionField gU (m.appTop a) =
      dominantFunctionFieldMap h (genericFibreToFunctionField gV a) := by
  have hη : h.base (genericPoint U) = genericPoint V :=
    ((tfae_isDominant_of_isIntegral h).out 1 2).mp (inferInstance : IsDominant h)
  have key := appTop_comp_genericFibreToFunctionField_aux gU gV h m hm hη.symm
  have keyapp := congrArg (fun φ => CommRingCat.Hom.hom φ a) key
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at keyapp
  have hdffm : dominantFunctionFieldMap h (genericFibreToFunctionField gV a) =
      (h.stalkMap (genericPoint U)).hom
        ((eqToHom (congrArg V.presheaf.stalk hη.symm)).hom
          ((genericFibreToFunctionField gV).hom a)) := by
    change (hη ▸ h.stalkMap (genericPoint U)).hom _ = _
    rw [← Stacks.Chow.stalkMap_eqToHom_eq_cast h (genericPoint U) (genericPoint V) hη]
    rfl
  rw [hdffm]
  exact keyapp

/-- **The naturality square of the comparison with the function field**, as an equality of ring
homomorphisms. -/
theorem comp_appTop_genericFibreToFunctionField {X U V : Scheme.{u}} [IrreducibleSpace X]
    [IsIntegral U] [IsIntegral V] (gU : U ⟶ X) (gV : V ⟶ X) [Flat gU] [Flat gV]
    (h : U ⟶ V) [IsDominant h]
    (m : pullback gU (genericPointInclusion X) ⟶ pullback gV (genericPointInclusion X))
    (hm : m ≫ pullback.fst gV (genericPointInclusion X) =
      pullback.fst gU (genericPointInclusion X) ≫ h) :
    (genericFibreToFunctionField gU).hom.comp m.appTop.hom =
      (dominantFunctionFieldMap h).comp (genericFibreToFunctionField gV).hom :=
  RingHom.ext fun a => genericFibreToFunctionField_appTop gU gV h m hm a

/-! ### Compatibility of the order of vanishing with restriction -/

/-- **The order of vanishing of an invertible global function on the generic fibre is compatible
with restriction along an étale morphism of `X`-schemes.** Restricting a section of `j_* 𝐆_{m,K}`
over `V` to an étale `V`-scheme `U` and taking its order of vanishing at a point `y` of `U` gives
the order of vanishing of the section at the image of `y` in `V`. -/
theorem genericFibreOrd_appTop {X U V : Scheme.{u}} [IrreducibleSpace X] [IsIntegral U]
    [IsIntegral V] [IsLocallyNoetherian U] [IsLocallyNoetherian V] (gU : U ⟶ X) (gV : V ⟶ X)
    [Flat gU] [Flat gV] (h : U ⟶ V) [Etale h]
    (m : pullback gU (genericPointInclusion X) ⟶ pullback gV (genericPointInclusion X))
    (hm : m ≫ pullback.fst gV (genericPointInclusion X) =
      pullback.fst gU (genericPointInclusion X) ≫ h)
    (y : U) (a : (Γ(pullback gV (genericPointInclusion X), ⊤))ˣ) :
    genericFibreOrd gU y (Additive.ofMul (Units.map m.appTop.hom.toMonoidHom a)) =
      genericFibreOrd gV (h.base y) (Additive.ofMul a) := by
  have : IsDominant h := isDominant_of_etale h
  erw [genericFibreOrd_apply, genericFibreOrd_apply,
    genericFibreToFunctionField_appTop gU gV h m hm,
    Stacks.Chow.ord_dominantFunctionFieldMap_of_etale h y]
  rfl

/-- **The morphism of generic fibres induced by a morphism of the small étale site of `X`.** -/
def etaleGenericFibreMap {X : Scheme.{u}} [IrreducibleSpace X] {U V : X.Etale} (φ : U ⟶ V) :
    pullback U.hom (genericPointInclusion X) ⟶ pullback V.hom (genericPointInclusion X) :=
  pullback.map U.hom (genericPointInclusion X) V.hom (genericPointInclusion X) φ.left (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, ← MorphismProperty.Over.w φ])
    (by rw [Category.comp_id, Category.id_comp])

/-- The morphism of generic fibres induced by `φ` lies over `φ.left`: composing it with the first
projection to `V` equals the first projection to `U` followed by `φ.left`. -/
@[simp]
theorem etaleGenericFibreMap_comp_fst {X : Scheme.{u}} [IrreducibleSpace X] {U V : X.Etale}
    (φ : U ⟶ V) :
    etaleGenericFibreMap φ ≫ pullback.fst V.hom (genericPointInclusion X) =
      pullback.fst U.hom (genericPointInclusion X) ≫ φ.left := by
  simp [etaleGenericFibreMap]

/-- **The order of vanishing of an invertible global function on the generic fibre is compatible
with restriction along a morphism `φ : U ⟶ V` of the small étale site of `X`:** restricting along
`Stacks.EtaleCohomology.etaleGenericFibreMap φ` and taking the order of vanishing at a point `y`
of `U` gives the order of vanishing at `φ.left.base y`. -/
@[stacks 03RI "the second map of the sequence is compatible with restriction along a morphism of
étale X-schemes, read on the order of vanishing at a point"]
theorem etaleGenericFibreOrd_appTop {X : Scheme.{u}} [IrreducibleSpace X] {U V : X.Etale}
    [IsIntegral U.left] [IsIntegral V.left] [IsLocallyNoetherian U.left]
    [IsLocallyNoetherian V.left] (φ : U ⟶ V) (y : U.left)
    (a : (Γ(pullback V.hom (genericPointInclusion X), ⊤))ˣ) :
    etaleGenericFibreOrd U y
        (Additive.ofMul (Units.map (etaleGenericFibreMap φ).appTop.hom.toMonoidHom a)) =
      etaleGenericFibreOrd V (φ.left.base y) (Additive.ofMul a) := by
  have : IsIntegral ((𝟭 Scheme).obj U.left) := inferInstanceAs (IsIntegral U.left)
  have : IsIntegral ((𝟭 Scheme).obj V.left) := inferInstanceAs (IsIntegral V.left)
  have : IsLocallyNoetherian ((𝟭 Scheme).obj U.left) :=
    inferInstanceAs (IsLocallyNoetherian U.left)
  have : IsLocallyNoetherian ((𝟭 Scheme).obj V.left) :=
    inferInstanceAs (IsLocallyNoetherian V.left)
  have : Etale U.hom := U.prop
  have : Etale V.hom := V.prop
  have : Etale φ.left := etale_of_etale_over φ.left (MorphismProperty.Over.w φ)
  exact genericFibreOrd_appTop (X := X) U.hom V.hom φ.left (etaleGenericFibreMap φ)
    (etaleGenericFibreMap_comp_fst φ) y a

end Stacks.EtaleCohomology

end
