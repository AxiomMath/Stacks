module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPresentationExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymExtPowFunctorial

/-!
# Naturality of the stalk of an exterior power

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerStalk` identifies the stalk at `x` of
the presheaf of sectionwise exterior powers `U ↦ ⋀ⁿ_{R(U)}(F(U))` with `⋀ⁿ_{R_x}(F_x)`, for one
presheaf of modules `F` at a time. This file makes that identification natural: the stalk of
`PresheafOfModules.extPowMap n ψ` is `⋀ⁿ` of the stalk map of `ψ`, both for the comparison
itself and for the transported one `PresheafOfModules.extPowStalkEquivOfStalkIso`, which is the
form in which a sheafified exterior power is read.

## Main results

* `PresheafOfModules.extPowStalkEquiv_naturality`: **the stalk of the sectionwise exterior power
  of a morphism is the exterior power of its stalk map.**
* `PresheafOfModules.extPowStalkEquivOfStalkIso_naturality`: the same for the comparison
  transported along morphisms which are stalk isomorphisms — a sheafification unit, in the
  intended use — with a morphism of the two targets extending the sectionwise one.
* `PresheafOfModules.extPowMap_app_ιMulti'`: the sectionwise exterior power of a morphism
  carries a wedge of local sections to the wedge of their images, as an equation in
  `PresheafOfModules.extPow`.
* `SheafOfModules.exteriorPowerStalkEquiv_naturality`: **the sheaf-level counterpart** — for
  exterior algebras `A` of `M` and `B` of `M'` in the sense of Stacks Section 17.21, the stalk
  of `SheafOfModules.GradedAlgebra.IsExteriorAlgebra.pieceMap` is `⋀ⁿ` of the stalk map, read
  through `SheafOfModules.exteriorPowerStalkEquiv`.

## Implementation notes

Both sides of the naturality square are linear maps out of `⋀ⁿ(F_x)` once the source stalk is
read through the comparison, so `exteriorPower.linearMap_ext` reduces the statement to a wedge
of `n` germs. There the two sides are computed by `extPowStalkL_germ_ιMulti` on each side and
`extPowMap_app_ιMulti` in between, after the `n` germs have been represented on one common open
neighbourhood — the same device `extPowStalkL_surjective` uses.

**The sheaf-level statement is the Tag 01CJ comparison, already proved.** `pieceMap hA hB f n`
and `(SheafOfModules.ExtPresentation.extDesc gen gen' hA hB f).app n` are the *same term*: both
unfold to `IsUniversal.desc hA B (f ≫ gen') _`, and the two `SquareZero` side conditions are
proofs of one `Prop`. So `SheafOfModules.exteriorPowerStalkEquiv_extDesc` discharges
`exteriorPowerStalkEquiv_naturality` outright, with no new wedge induction.

**The binders of the sheaf-level statement must be section `variable`s.** Written out inline in
the theorem signature the very same statement exhausts the default `maxHeartbeats` at `whnf`
while elaborating the application of `exteriorPower.map n (stalkMapL y (valHom f))` to
`exteriorPowerStalkEquiv A gen hA n y q`; as section variables it elaborates in a second. The
difference is elaboration order only — nothing about the statement changes — and no raised
heartbeat budget is needed.

## References

* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace PresheafOfModules

variable {X : TopCat.{u}} {R : X.Presheaf CommRingCat.{u}}
  {F F' : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})} (x : X)

/-- The sectionwise exterior power of a morphism carries a wedge of local sections to the wedge
of their images. -/
theorem extPowMap_app_ιMulti' (n : ℕ) (φ : F ⟶ F') (U : Opens X) (s : Fin n → F.obj (op U)) :
    (extPowMap n φ).app (op U)
        (exteriorPower.ιMulti
          ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) n s) =
      exteriorPower.ιMulti ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op U)) n
        fun i => φ.app (op U) (s i) :=
  Subtype.ext
    ((extPowMap_app_ιMulti n φ (op U) s _ (exteriorPower.ιMulti_apply_coe _ n s)).trans
      (exteriorPower.ιMulti_apply_coe _ n _).symm)

/-- **Exterior powers commute with stalks naturally in the presheaf of modules.** The stalk of
the sectionwise exterior power of `φ` is the exterior power of the stalk map. Both sides are
linear maps out of `⋀ⁿ(F_x)` once the source is read through
`PresheafOfModules.extPowStalkEquiv`, so it is enough to compare them on a wedge of `n` germs,
and there both carry it to the wedge of the images of those germs. -/
theorem extPowStalkEquiv_naturality (n : ℕ) (φ : F ⟶ F')
    (t : ↑(TopCat.Presheaf.stalk (extPow n F).presheaf x)) :
    extPowStalkEquiv F' x n (stalkMapL x (extPowMap n φ) t) =
      exteriorPower.map n (stalkMapL x φ) (extPowStalkEquiv F x n t) := by
  have key : (extPowStalkL F' x n).comp ((stalkMapL x (extPowMap n φ)).comp
        (extPowStalkEquiv F x n).symm.toLinearMap) =
      exteriorPower.map n (stalkMapL x φ) := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v => ?_)
    choose U hU t₀ ht using fun i : Fin n => TopCat.Presheaf.exists_germ_eq F.presheaf (v i)
    have hW : x ∈ (⨅ i, U i : Opens X) := by
      have h : x ∈ (↑(⨅ i, U i) : Set X) := by
        rw [Opens.coe_iInf]
        exact Set.mem_iInter.2 hU
      exact h
    set W : Opens X := ⨅ i, U i with hWdef
    set s : Fin n → F.obj (op W) := fun i => F.map (homOfLE (iInf_le U i)).op (t₀ i) with hs
    have hgerm : ∀ i, TopCat.Presheaf.germ F.presheaf W x hW (s i) = v i := fun i =>
      (TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE (iInf_le U i)) x hW (t₀ i)).trans (ht i)
    have hsymm : (extPowStalkEquiv F x n).symm
        (exteriorPower.ιMulti ↑(R.stalk x) n v) =
        TopCat.Presheaf.germ (extPow n F).presheaf W x hW
          (exteriorPower.ιMulti
            ((R ⋙ forget₂ CommRingCat.{u} RingCat.{u}).obj (op W)) n s) :=
      ((extPowStalkEquiv F x n).symm_apply_eq).2
        ((extPowStalkL_germ_ιMulti F x n W hW s).trans
          (congrArg (exteriorPower.ιMulti ↑(R.stalk x) n) (funext hgerm))).symm
    refine Eq.trans (congrArg (fun z => extPowStalkL F' x n (stalkMapL x (extPowMap n φ) z))
      hsymm) ?_
    refine Eq.trans (congrArg (extPowStalkL F' x n)
      (stalkMapL_germ x (extPowMap n φ) W hW _)) ?_
    refine Eq.trans (congrArg (fun z => extPowStalkL F' x n
      (TopCat.Presheaf.germ (extPow n F').presheaf W x hW z))
      (extPowMap_app_ιMulti' n φ W s)) ?_
    refine (extPowStalkL_germ_ιMulti F' x n W hW fun i => φ.app (op W) (s i)).trans ?_
    refine Eq.trans ?_ (exteriorPower.map_apply_ιMulti (stalkMapL x φ) v).symm
    exact congrArg (exteriorPower.ιMulti ↑(R.stalk x) n)
      (funext fun i => (stalkMapL_germ x φ W hW (s i)).symm.trans
        (congrArg (stalkMapL x φ) (hgerm i)))
  have h := LinearMap.congr_fun key (extPowStalkEquiv F x n t)
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] at h
  exact h

/-- The stalk map of a composite is the composite of the stalk maps. -/
theorem stalkMapL_comp_apply
    {P Q S : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (α : P ⟶ Q) (β : Q ⟶ S) (t : ↑(TopCat.Presheaf.stalk P.presheaf x)) :
    stalkMapL x β (stalkMapL x α t) = stalkMapL x (α ≫ β) t := by
  obtain ⟨U, hU, y, rfl⟩ := TopCat.Presheaf.exists_germ_eq P.presheaf t
  refine Eq.trans (congrArg (stalkMapL x β) (stalkMapL_germ x α U hU y)) ?_
  exact (stalkMapL_germ x β U hU _).trans (stalkMapL_germ x (α ≫ β) U hU y).symm

/-- **The identification of the stalk of a sheafified exterior power with the exterior power of
the stalk is natural.** If `φ` and `φ'` exhibit `Q` and `Q'` as having the stalks of the
sectionwise exterior powers of `F` and `F'`, and `g : Q ⟶ Q'` extends the sectionwise exterior
power of `ψ : F ⟶ F'`, then on stalks `g` is `⋀ⁿ` of the stalk map of `ψ`. -/
theorem extPowStalkEquivOfStalkIso_naturality (n : ℕ) (ψ : F ⟶ F')
    {Q Q' : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (φ : extPow n F ⟶ Q)
    (hφ : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ((toPresheaf _).map φ)))
    (φ' : extPow n F' ⟶ Q')
    (hφ' : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ((toPresheaf _).map φ')))
    (g : Q ⟶ Q') (hg : extPowMap n ψ ≫ φ' = φ ≫ g)
    (q : ↑(TopCat.Presheaf.stalk Q.presheaf x)) :
    extPowStalkEquivOfStalkIso F' x n φ' hφ' (stalkMapL x g q) =
      exteriorPower.map n (stalkMapL x ψ) (extPowStalkEquivOfStalkIso F x n φ hφ q) := by
  obtain ⟨p, rfl⟩ := (stalkLinearEquiv x φ hφ).surjective q
  have hsrc : extPowStalkEquivOfStalkIso F x n φ hφ (stalkLinearEquiv x φ hφ p) =
      extPowStalkEquiv F x n p :=
    congrArg (extPowStalkEquiv F x n) ((stalkLinearEquiv x φ hφ).symm_apply_apply p)
  have htgt : stalkMapL x g (stalkLinearEquiv x φ hφ p) =
      stalkLinearEquiv x φ' hφ' (stalkMapL x (extPowMap n ψ) p) :=
    (stalkMapL_comp_apply x φ g p).trans
      ((congrArg (fun k => stalkMapL x k p) hg).symm.trans
        (stalkMapL_comp_apply x (extPowMap n ψ) φ' p).symm)
  rw [hsrc, htgt]
  refine Eq.trans (congrArg (extPowStalkEquiv F' x n)
    ((stalkLinearEquiv x φ' hφ').symm_apply_apply _)) ?_
  exact extPowStalkEquiv_naturality x n ψ p

end PresheafOfModules

/-! ### The sheaf-level naturality square -/

namespace SheafOfModules

open CategoryTheory.Sheaf SheafOfModules.SymPresentation

variable {Y : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥Y) CommRingCat.{u}}
  {M M' : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥Y) Osharp)}
  {A B : GradedAlgebra.{u, u} (toRingCat (Opens.grothendieckTopology ↥Y) Osharp)}
  {gen : M ⟶ A.piece 1} {gen' : M' ⟶ B.piece 1}
  (hA : GradedAlgebra.IsExteriorAlgebra A gen) (hB : GradedAlgebra.IsExteriorAlgebra B gen')
  (f : M ⟶ M')

/-- **The stalk of the exterior power of a morphism of sheaves of modules is the exterior power
of its stalk map.** Read through the comparison `SheafOfModules.exteriorPowerStalkEquiv` of Tag
01CH, the stalk at `y` of the degree-`n` map induced by `f : M ⟶ M'` between exterior algebras
`A` of `M` and `B` of `M'` is `⋀ⁿ` of the stalk map of `f`.

The induced map `IsExteriorAlgebra.pieceMap` and the comparison homomorphism
`SheafOfModules.ExtPresentation.extDesc` of Tag 01CJ are the same term, so this is
`SheafOfModules.ExtPresentation.exteriorPowerStalkEquiv_extDesc`. -/
theorem exteriorPowerStalkEquiv_naturality (n : ℕ) (y : ↥Y)
    (q : ↑(TopCat.Presheaf.stalk (A.piece (n : ℤ)).val.presheaf y)) :
    exteriorPowerStalkEquiv B gen' hB n y
        (PresheafOfModules.stalkMapL y
          (valHom (GradedAlgebra.IsExteriorAlgebra.pieceMap hA hB f (n : ℤ))) q) =
      exteriorPower.map n (PresheafOfModules.stalkMapL y (valHom f))
        (exteriorPowerStalkEquiv A gen hA n y q) :=
  ExtPresentation.exteriorPowerStalkEquiv_extDesc gen gen' hA hB f n y q

end SheafOfModules

end
