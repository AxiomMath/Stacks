module

public import StacksFrontier.CategoryTheory.Adjunction.UniqueCompApp

/-!
# The transpose of the comparison of two composite left adjoints

`CategoryTheory.Adjunction.leftAdjointUniq_comp_ofNatIsoRight_hom_app` gives the forward component
of the comparison of the two composite left adjoints `Ef ⋙ B` and `Fu ⋙ Sf` of a natural
isomorphism `δ : Si ⋙ U ≅ V ⋙ Ei` as a composite of five factors, the last of which is the counit
of `adjB`.  A consumer comparing that component with something else almost never compares it
directly: the component is a morphism out of `B (Ef K)`, and the only handle on such a morphism is
its transpose under `adjB`.

This file records that transpose.  Four of the five factors of the component formula are `B`
applied to one morphism, and the fifth is the counit of `adjB`, so the component is the inverse
transpose of a single morphism `Ef K ⟶ V (Sf (Fu K))`; transposing back therefore cancels
everything and returns that morphism, which is the unit of the second composite adjunction read
through `adjE`.

The gain is that the right-hand side no longer mentions `B`, `adjB` or the comparison at all: it is
the unit of `adjF` pushed forward by `Ef`, followed by the mate of `δ` across the two adjunctions
`adjE` and `adjS`.  That is the form in which the comparison of derived extension of scalars with
the scalar lift can be evaluated against a chain-level comparison.

## Main results

* `CategoryTheory.Adjunction.unit_comp_map_leftAdjointUniq_comp_ofNatIsoRight_hom_app`: the
  transpose under `adjB` of the forward component of the comparison.
* `CategoryTheory.Adjunction.unit_comp_map_leftAdjointUniq_comp_ofNatIsoRight_hom_app_comp`: the
  same with a morphism out of the comparison's target appended, which is how it is used -- the
  appended morphism passes to the left of both the counit and `δ`.
* `CategoryTheory.Adjunction.unit_comp_map_leftAdjointUniq_comp_ofNatIsoRight_hom_app_iso_comp`:
  the same with a presentation of the comparison's source in front as well.
* `CategoryTheory.Adjunction.eq_of_unit_comp_map_eq`: two morphisms out of a left adjoint with
  the same transpose agree.
* `CategoryTheory.Adjunction.unit_comp_map_comp_iso_hom_eq`: the transpose of a two-factor
  composite followed by an isomorphism, from values for the two factors.
* `CategoryTheory.Functor.map_comp_eq_comp_of_chain`: a four-step chain of values for one
  composite collapses it to a two-factor composite.
* `CategoryTheory.Adjunction.eq_comp_of_transpose_value`: an equation of morphisms out of a left
  adjoint, from a value for each of the two transposes.
* `CategoryTheory.Adjunction.eq_comp_of_transpose_chain`: the same with the value of the first
  transpose supplied as a four-step chain.

## Implementation notes

The proof is the unit--counit triangle of `adjB` and nothing else: the four leading factors of the
component formula are folded into one `B.map` by functoriality, and the transpose of
`B.map θ ≫ adjB.counit.app Z` is `θ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.Functor

/-- **A four-step chain of values collapses a composite.**

Given a morphism `lhs` which `h7` rewrites as `Ef.map gg ≫ sl ≫ qcc`, a second spelling `qg` of
`gg` from `h8`, a value `h9` for `Ef.map qg ≫ sl` as a presentation `ih` followed by `ql`, and a
name `w` for `ql ≫ qcc` from `hfin`, the morphism `lhs` is `ih ≫ w`.

Every object and morphism is a variable, so the four hypotheses can be discharged in four separate
declarations and the collapse itself costs nothing. -/
theorem map_comp_eq_comp_of_chain {A' B' : Type*} [Category* A'] [Category* B'] (Ef : A' ⥤ B')
    {a₀ a₂ : A'} {k P₁ d : B'} {lhs : Ef.obj a₀ ⟶ d} {gg qg : a₀ ⟶ a₂}
    {sl : Ef.obj a₂ ⟶ P₁} {qcc : P₁ ⟶ d} {ih : Ef.obj a₀ ⟶ k} {ql : k ⟶ P₁} {w : k ⟶ d}
    (h7 : lhs = Ef.map gg ≫ sl ≫ qcc) (h8 : gg = qg)
    (h9 : Ef.map qg ≫ sl = ih ≫ ql) (hfin : ql ≫ qcc = w) :
    lhs = ih ≫ w := by
  rw [h7, h8, ← Category.assoc, h9, Category.assoc, hfin]

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C₀ C₁ C₁' C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₁'] [Category* C₂]
  {Ef : C₀ ⥤ C₁'} {Ei : C₁' ⥤ C₀} {B : C₁' ⥤ C₂} {V : C₂ ⥤ C₁'}
  {Fu : C₀ ⥤ C₁} {U : C₁ ⥤ C₀} {Sf : C₁ ⥤ C₂} {Si : C₂ ⥤ C₁}

/-- **The transpose of the forward component of the comparison of two composite left adjoints.**

The component at `K` of
`CategoryTheory.Adjunction.leftAdjointUniq ((adjE.comp adjB)) ((adjF.comp adjS).ofNatIsoRight δ)`
is a morphism `B (Ef K) ⟶ Sf (Fu K)`; its transpose under `adjB` is the unit of `adjF` at `K`
pushed forward by `Ef`, then `U` applied to the unit of `adjS`, then `δ`, then the counit of
`adjE`.

Neither `B` nor `adjB` occurs on the right-hand side.  This is what makes the comparison
computable: the four leading factors of
`CategoryTheory.Adjunction.leftAdjointUniq_comp_ofNatIsoRight_hom_app` are `B` applied to exactly
this morphism, and the fifth is the counit of `adjB`, so the transpose is the unit--counit triangle
of `adjB`. -/
theorem unit_comp_map_leftAdjointUniq_comp_ofNatIsoRight_hom_app
    (adjE : Ef ⊣ Ei) (adjB : B ⊣ V) (adjF : Fu ⊣ U) (adjS : Sf ⊣ Si)
    (δ : Si ⋙ U ≅ V ⋙ Ei) (K : C₀) :
    adjB.unit.app (Ef.obj K) ≫
        V.map (((adjE.comp adjB).leftAdjointUniq
          ((adjF.comp adjS).ofNatIsoRight δ)).hom.app K) =
      Ef.map (adjF.unit.app K ≫ U.map (adjS.unit.app (Fu.obj K)) ≫
          δ.hom.app (Sf.obj (Fu.obj K))) ≫
        adjE.counit.app (V.obj (Sf.obj (Fu.obj K))) := by
  have key : ∀ (Z : C₂) (θ : Ef.obj K ⟶ V.obj Z),
      adjB.unit.app (Ef.obj K) ≫ V.map (B.map θ ≫ adjB.counit.app Z) = θ := fun Z θ => by
    simp
  rw [leftAdjointUniq_comp_ofNatIsoRight_hom_app, show
      B.map (Ef.map (adjF.unit.app K)) ≫
          B.map (Ef.map (U.map (adjS.unit.app (Fu.obj K)))) ≫
            B.map (Ef.map (δ.hom.app (Sf.obj (Fu.obj K)))) ≫
              B.map (adjE.counit.app (V.obj (Sf.obj (Fu.obj K)))) ≫
                adjB.counit.app (Sf.obj (Fu.obj K)) =
        B.map (Ef.map (adjF.unit.app K ≫ U.map (adjS.unit.app (Fu.obj K)) ≫
              δ.hom.app (Sf.obj (Fu.obj K))) ≫
            adjE.counit.app (V.obj (Sf.obj (Fu.obj K)))) ≫
          adjB.counit.app (Sf.obj (Fu.obj K)) from by
      simp only [Functor.map_comp, Category.assoc]]
  exact key _ _


/-- **The transpose of the comparison, followed by a morphism of the target.**

`CategoryTheory.Adjunction.unit_comp_map_leftAdjointUniq_comp_ofNatIsoRight_hom_app` with a
morphism `psi` out of `Sf (Fu X)` appended.  Appending it moves the whole bookkeeping inside the
one morphism the right-hand side pushes forward along `Ef`: the counit of `adjE` is natural, so
`psi` passes to the left of it, and `δ` is natural, so it passes further to the left of `δ` as
`U` applied to `Si psi`.

This is the form a consumer uses.  The comparison never occurs alone in practice -- it occurs
followed by a presentation of its target as a class -- and the right-hand side here mentions only
the two units, `δ` at the *target of* `psi`, and the counit of `adjE`, so every factor can be
evaluated separately. -/
theorem unit_comp_map_leftAdjointUniq_comp_ofNatIsoRight_hom_app_comp
    {C₀ C₁ C₁' C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₁'] [Category* C₂]
    {Fu : C₀ ⥤ C₁} {U : C₁ ⥤ C₀} {B : C₁' ⥤ C₂} {V : C₂ ⥤ C₁'}
    (adjE : C₀ ≌ C₁') (adjS : C₁ ≌ C₂) (adjB : B ⊣ V) (adjF : Fu ⊣ U)
    (δ : adjS.inverse ⋙ U ≅ V ⋙ adjE.inverse) (X : C₀) (W : C₂)
    (psi : adjS.functor.obj (Fu.obj X) ⟶ W) :
    adjB.unit.app (adjE.functor.obj X) ≫
          V.map (((adjE.toAdjunction.comp adjB).leftAdjointUniq
            ((adjF.comp adjS.toAdjunction).ofNatIsoRight δ)).hom.app X) ≫ V.map psi =
      adjE.functor.map (adjF.unit.app X ≫
            U.map (adjS.toAdjunction.unit.app (Fu.obj X) ≫ adjS.inverse.map psi) ≫
          δ.hom.app W) ≫ adjE.counitIso.hom.app (V.obj W) := by
  rw [← Category.assoc, unit_comp_map_leftAdjointUniq_comp_ofNatIsoRight_hom_app,
    Category.assoc]
  rw [show adjE.toAdjunction.counit.app (V.obj (adjS.functor.obj (Fu.obj X))) ≫ V.map psi =
        adjE.functor.map (adjE.inverse.map (V.map psi)) ≫ adjE.counitIso.hom.app (V.obj W) from
      (adjE.counitIso.hom.naturality (V.map psi)).symm,
    ← Category.assoc, ← Functor.map_comp]
  refine congrArg (fun z => adjE.functor.map z ≫ adjE.counitIso.hom.app (V.obj W)) ?_
  rw [Functor.map_comp]
  simp only [Category.assoc]
  exact congrArg (fun z => adjF.unit.app X ≫ U.map (adjS.toAdjunction.unit.app (Fu.obj X)) ≫ z)
    (δ.hom.naturality psi).symm


/-- **The transpose of the comparison, with a presentation of its source and a morphism of its
target.**

`CategoryTheory.Adjunction.unit_comp_map_leftAdjointUniq_comp_ofNatIsoRight_hom_app_comp`
preceded by `B` applied to the inverse of an isomorphism `ι` presenting `Ef X`, which is how the
comparison occurs: both of its ends are reached through presentations.  The prefix passes to the
front by naturality of the unit of `adjB`.

The morphism `g` is taken as a variable with its value as a hypothesis, rather than written into
the conclusion, so that a consumer can hand over whatever spelling of it the next lemma in its
chain expects. -/
theorem unit_comp_map_leftAdjointUniq_comp_ofNatIsoRight_hom_app_iso_comp
    {C₀ C₁ C₁' C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₁'] [Category* C₂]
    {Fu : C₀ ⥤ C₁} {U : C₁ ⥤ C₀} {B : C₁' ⥤ C₂} {V : C₂ ⥤ C₁'}
    (adjE : C₀ ≌ C₁') (adjS : C₁ ≌ C₂) (adjB : B ⊣ V) (adjF : Fu ⊣ U)
    (δ : adjS.inverse ⋙ U ≅ V ⋙ adjE.inverse) (X : C₀) {Z : C₁'}
    (ι : adjE.functor.obj X ≅ Z) (W : C₂) (psi : adjS.functor.obj (Fu.obj X) ⟶ W)
    (g : X ⟶ U.obj (adjS.inverse.obj W))
    (hg : g = adjF.unit.app X ≫
      U.map (adjS.toAdjunction.unit.app (Fu.obj X) ≫ adjS.inverse.map psi)) :
    adjB.unit.app Z ≫
          V.map (B.map ι.inv ≫ ((adjE.toAdjunction.comp adjB).leftAdjointUniq
            ((adjF.comp adjS.toAdjunction).ofNatIsoRight δ)).hom.app X ≫ psi) =
      ι.inv ≫ adjE.functor.map (g ≫ δ.hom.app W) ≫ adjE.counitIso.hom.app (V.obj W) := by
  have hn : adjB.unit.app Z ≫ V.map (B.map ι.inv) =
      ι.inv ≫ adjB.unit.app (adjE.functor.obj X) := (adjB.unit.naturality ι.inv).symm
  rw [hg, Functor.map_comp, Functor.map_comp, ← Category.assoc, hn, Category.assoc,
    unit_comp_map_leftAdjointUniq_comp_ofNatIsoRight_hom_app_comp adjE adjS adjB adjF δ X W psi,
    Category.assoc]


/-- **Right-cancelling the unit of an adjunction.**  Two morphisms out of `B X` with the same
transpose agree, the transpose being a bijection. -/
theorem eq_of_unit_comp_map_eq {C D : Type*} [Category* C] [Category* D] {Lf : C ⥤ D}
    {Rg : D ⥤ C} (adj : Lf ⊣ Rg) {X : C} {Y : D} {g₁ g₂ : Lf.obj X ⟶ Y}
    (h : adj.unit.app X ≫ Rg.map g₁ = adj.unit.app X ≫ Rg.map g₂) : g₁ = g₂ := by
  refine (adj.homEquiv X Y).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact h


/-- **The transpose of a two-factor composite, followed by an isomorphism.**

Given a value `h1` for the transpose of the first factor and a value `h2` for the resulting
composite with the second, the transpose of `al ≫ qc` followed by `fh` is the product of the two
values.  This is the right-hand half of
`CategoryTheory.Adjunction.eq_comp_of_transpose_chain`, isolated so that it can be discharged
without any rewriting in the ambient goal. -/
theorem unit_comp_map_comp_iso_hom_eq {C D : Type*} [Category* C] [Category* D]
    {Bf : C ⥤ D} {Vf : D ⥤ C} (adjB : Bf ⊣ Vf)
    {k e d : C} {y z : D} {al : Bf.obj k ⟶ y} {qc : y ⟶ z}
    {qu : k ⟶ e} {fi : e ⟶ Vf.obj y} {qrc : e ⟶ d} (fh : Vf.obj z ≅ d)
    (h1 : adjB.unit.app k ≫ Vf.map al = qu ≫ fi)
    (h2 : fi ≫ Vf.map qc = qrc ≫ fh.inv) :
    (adjB.unit.app k ≫ Vf.map (al ≫ qc)) ≫ fh.hom = qu ≫ qrc := by
  rw [Functor.map_comp, ← Category.assoc (adjB.unit.app k) (Vf.map al) (Vf.map qc), h1,
    Category.assoc qu fi (Vf.map qc), h2, Category.assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- **An equation of morphisms out of a left adjoint, from a value for each transpose.**

The shape in which an identification of two morphisms `Bf k ⟶ z` is reached when both are only
known through their transposes.  The left-hand morphism `g` has its transpose given by `hA` as the
inverse of a presentation `ι` followed by a morphism pushed forward along `Ef` and a trailing
morphism; `hL` evaluates that composite, once followed by the isomorphism `fh`, as `ι.hom ≫ w`;
and `hB` says the transpose of the right-hand morphism, followed by `fh`, is the same `w`.
Cancelling the presentation, the isomorphism and the transpose gives the equation.

Everything is a variable, so an instantiation costs nothing: each hypothesis is discharged
separately against whichever lemma values that factor.  That matters in practice, because the
three hypotheses are the only places where the ambient composites have to be written down, and a
consumer that supplied them inline would elaborate all three against one heartbeat budget. -/
theorem eq_comp_of_transpose_value
    {A' B' D' : Type*} [Category* A'] [Category* B'] [Category* D']
    {Bf : B' ⥤ D'} {Vf : D' ⥤ B'} (adjB : Bf ⊣ Vf) (Ef : A' ⥤ B')
    {a₀ a₁ : A'} {k d : B'} {y z : D'}
    {g : Bf.obj k ⟶ z} {al : Bf.obj k ⟶ y} {qc : y ⟶ z}
    (ι : Ef.obj a₀ ≅ k) (fh : Vf.obj z ≅ d)
    {gdh : a₀ ⟶ a₁} {cc : Ef.obj a₁ ⟶ Vf.obj z} {w : k ⟶ d}
    (hA : adjB.unit.app k ≫ Vf.map g = ι.inv ≫ Ef.map gdh ≫ cc)
    (hL : Ef.map gdh ≫ cc ≫ fh.hom = ι.hom ≫ w)
    (hB : (adjB.unit.app k ≫ Vf.map (al ≫ qc)) ≫ fh.hom = w) :
    g = al ≫ qc := by
  have hLv : (ι.inv ≫ Ef.map gdh ≫ cc) ≫ fh.hom = w := by
    rw [Category.assoc, Category.assoc, hL, Iso.inv_hom_id_assoc]
  refine eq_of_unit_comp_map_eq adjB ?_
  rw [hA]
  exact (Iso.cancel_iso_hom_right _ _ fh).mp (hLv.trans hB.symm)

/-- **An equation of morphisms out of a left adjoint, from a chain of values for its two
transposes.**

`CategoryTheory.Adjunction.eq_comp_of_transpose_value` with the value of the first transpose
supplied as the four-step chain `CategoryTheory.Functor.map_comp_eq_comp_of_chain` collapses:
`hs7` rewrites the composite as a morphism pushed forward along `Ef` followed by two factors,
`hs8` identifies that morphism with a second spelling, `hs9` absorbs the first of the two factors
into the presentation `ι`, and `hfin` names the rest. -/
theorem eq_comp_of_transpose_chain
    {A' B' D' : Type*} [Category* A'] [Category* B'] [Category* D']
    {Bf : B' ⥤ D'} {Vf : D' ⥤ B'} (adjB : Bf ⊣ Vf) (Ef : A' ⥤ B')
    {a₀ a₁ a₂ : A'} {k d P₁ : B'} {y z : D'}
    {g : Bf.obj k ⟶ z} {al : Bf.obj k ⟶ y} {qc : y ⟶ z}
    (ι : Ef.obj a₀ ≅ k) (fh : Vf.obj z ≅ d)
    {gdh : a₀ ⟶ a₁} {cc : Ef.obj a₁ ⟶ Vf.obj z}
    {gg₂ qg : a₀ ⟶ a₂} {sl : Ef.obj a₂ ⟶ P₁} {qcc : P₁ ⟶ d}
    {ql : k ⟶ P₁} {w : k ⟶ d}
    (hA : adjB.unit.app k ≫ Vf.map g = ι.inv ≫ Ef.map gdh ≫ cc)
    (hs7 : Ef.map gdh ≫ cc ≫ fh.hom = Ef.map gg₂ ≫ sl ≫ qcc)
    (hs8 : gg₂ = qg)
    (hs9 : Ef.map qg ≫ sl = ι.hom ≫ ql)
    (hfin : ql ≫ qcc = w)
    (hB : (adjB.unit.app k ≫ Vf.map (al ≫ qc)) ≫ fh.hom = w) :
    g = al ≫ qc :=
  eq_comp_of_transpose_value adjB Ef ι fh hA
    (Functor.map_comp_eq_comp_of_chain Ef hs7 hs8 hs9 hfin) hB

end CategoryTheory.Adjunction

end
