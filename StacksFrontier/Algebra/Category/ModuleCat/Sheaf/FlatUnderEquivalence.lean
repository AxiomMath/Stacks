module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackFlatInverseImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteUpSheafificationPullback

/-!
# Flatness under an equivalence of ringed topoi

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi whose direct image on sheaves
of sets is an equivalence and whose structure map `f♯` is an isomorphism. A sheaf of
`O_D`-modules `F` is flat if and only if its pullback `f^* F` is flat.

The forward implication is Modules on Sites, Lemma 05VD, which holds for any morphism of ringed
topoi. The reverse one applies 05VD to the inverse morphism and carries the conclusion back along
the identification of the round trip `(f⁻¹)^* f^* F ≅ F`, flatness being invariant under
isomorphism.

## Main results

* `AlgebraicGeometry.RingedToposHom.isFlat_iff_pullbackModules`: flatness is intrinsic under an
  equivalence of ringed topoi.

## Implementation notes

The two ringed topoi have independent object and morphism universes; only the universe of the
sections is shared, which the round-trip isomorphism needs. Lemma 05VD itself is stated at six
independent universes, so nothing else constrains them. This is the generality in which the
small Zariski site of a scheme, whose objects live one universe up, is compared with the site of
opens of the scheme. `Stacks.Sheaves.LocalTypeComparison.isFlat_iff` is the special case in
which all six universes agree.

## References

* [Stacks, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RingedToposHom

universe v u v' u' w

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w)]
  [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : Y.C, HasWeakSheafify (Y.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

omit [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : Y.C, HasWeakSheafify (Y.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **Flatness is intrinsic under an equivalence of ringed topoi.** A sheaf of modules on the
target of a morphism of ringed topoi whose direct image is an equivalence and whose structure
map is invertible is flat if and only if its pullback is flat. -/
theorem isFlat_iff_pullbackModules (f : RingedToposHom X Y)
    [f.toToposHom.pushforward.IsEquivalence] [IsIso f.fSharp]
    (F : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)) :
    Stacks.SheafOfModules.IsFlat (O := Y.O) F ↔
      Stacks.SheafOfModules.IsFlat (O := X.O) ((f.toModulesHom.pullbackModules).obj F) := by
  refine ⟨fun hF ↦ ?_, fun hP ↦ ?_⟩
  · exact Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules f.toModulesHom F hF
  · exact Stacks.ModuleUp.isFlat_of_iso_anySite (O := Y.O) (pullbackModulesInverseObjIso f F)
      (Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules (inverse f).toModulesHom _ hP)

end AlgebraicGeometry.RingedToposHom

end
